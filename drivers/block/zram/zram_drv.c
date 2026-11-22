/*
 * Compressed RAM block device
 *
 * Copyright (C) 2008, 2009, 2010  Nitin Gupta
 *               2012, 2013 Minchan Kim
 *
 * This code is released using a dual license strategy: BSD/GPL
 * You can choose the licence that better fits your requirements.
 *
 * Released under the terms of 3-clause BSD License
 * Released under the terms of GNU General Public License Version 2.0
 *
 */

#define KMSG_COMPONENT "zram"
#define pr_fmt(fmt) KMSG_COMPONENT ": " fmt

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/bio.h>
#include <linux/bitops.h>
#include <linux/blkdev.h>
#include <linux/buffer_head.h>
#include <linux/device.h>
#include <linux/genhd.h>
#include <linux/highmem.h>
#include <linux/slab.h>
#include <linux/backing-dev.h>
#include <linux/string.h>
#include <linux/vmalloc.h>
#include <linux/err.h>
#include <linux/idr.h>
#include <linux/sysfs.h>
#include <linux/debugfs.h>
#include <linux/cpuhotplug.h>
#include <linux/part_stat.h>
#include <linux/rcupdate.h>
#ifdef CONFIG_ZRAM_ANDROID_IOCTL
#include <linux/pagewalk.h>
#include <linux/pid.h>
#include <linux/sched/mm.h>
#include <linux/sched/task.h>
#include <linux/swap.h>
#include <linux/swapops.h>
#include <uapi/linux/zram_ioctl.h>
#endif

#include "zram_drv.h"

static DEFINE_IDR(zram_index_idr);
/* idr index must be protected */
static DEFINE_MUTEX(zram_index_mutex);

static int zram_major;
static const char *default_compressor = "lzo-rle";

/* Module params (documentation at end) */
static unsigned int num_devices = 1;
/*
 * Pages that compress to sizes equals or greater than this are stored
 * uncompressed in memory.
 */
static size_t huge_class_size;

static const struct block_device_operations zram_devops;
static const struct block_device_operations zram_wb_devops;

static void zram_free_page(struct zram *zram, size_t index);
static int zram_read_from_zspool(struct zram *zram, struct page *page,
				 u32 index);


static int zram_slot_trylock(struct zram *zram, u32 index)
{
	return bit_spin_trylock(ZRAM_LOCK, &zram->table[index].flags);
}

static void zram_slot_lock(struct zram *zram, u32 index)
{
	bit_spin_lock(ZRAM_LOCK, &zram->table[index].flags);
}

static void zram_slot_unlock(struct zram *zram, u32 index)
{
	bit_spin_unlock(ZRAM_LOCK, &zram->table[index].flags);
}

static inline bool init_done(struct zram *zram)
{
	return zram->disksize;
}

static inline struct zram *dev_to_zram(struct device *dev)
{
	return (struct zram *)dev_to_disk(dev)->private_data;
}

static unsigned long zram_get_handle(struct zram *zram, u32 index)
{
	return zram->table[index].handle;
}

static void zram_set_handle(struct zram *zram, u32 index, unsigned long handle)
{
	zram->table[index].handle = handle;
}

/* flag operations require table entry bit_spin_lock() being held */
static bool zram_test_flag(struct zram *zram, u32 index,
			enum zram_pageflags flag)
{
	return zram->table[index].flags & BIT(flag);
}

static void zram_set_flag(struct zram *zram, u32 index,
			enum zram_pageflags flag)
{
	zram->table[index].flags |= BIT(flag);
}

static void zram_clear_flag(struct zram *zram, u32 index,
			enum zram_pageflags flag)
{
	zram->table[index].flags &= ~BIT(flag);
}

static inline void zram_set_element(struct zram *zram, u32 index,
			unsigned long element)
{
	zram->table[index].element = element;
}

static unsigned long zram_get_element(struct zram *zram, u32 index)
{
	return zram->table[index].element;
}

static size_t zram_get_obj_size(struct zram *zram, u32 index)
{
	return zram->table[index].flags & (BIT(ZRAM_FLAG_SHIFT) - 1);
}

static void zram_set_obj_size(struct zram *zram,
					u32 index, size_t size)
{
	unsigned long flags = zram->table[index].flags >> ZRAM_FLAG_SHIFT;

	zram->table[index].flags = (flags << ZRAM_FLAG_SHIFT) | size;
}

static inline bool zram_allocated(struct zram *zram, u32 index)
{
	return zram_get_obj_size(zram, index) ||
			zram_test_flag(zram, index, ZRAM_SAME) ||
			zram_test_flag(zram, index, ZRAM_WB);
}

#if PAGE_SIZE != 4096
static inline bool is_partial_io(struct bio_vec *bvec)
{
	return bvec->bv_len != PAGE_SIZE;
}
#else
static inline bool is_partial_io(struct bio_vec *bvec)
{
	return false;
}
#endif

static inline void zram_set_priority(struct zram *zram, u32 index, u32 prio)
{
	prio &= ZRAM_COMP_PRIORITY_MASK;
	/*
	 * Clear previous priority value first, in case if we recompress
	 * further an already recompressed page
	 */
	zram->table[index].flags &= ~(ZRAM_COMP_PRIORITY_MASK <<
				      ZRAM_COMP_PRIORITY_BIT1);
	zram->table[index].flags |= (prio << ZRAM_COMP_PRIORITY_BIT1);
}

static inline u32 zram_get_priority(struct zram *zram, u32 index)
{
	u32 prio = zram->table[index].flags >> ZRAM_COMP_PRIORITY_BIT1;

	return prio & ZRAM_COMP_PRIORITY_MASK;
}

#if defined(CONFIG_ZRAM_WRITEBACK) || defined(CONFIG_ZRAM_MULTI_COMP)
struct zram_pp_slot {
	unsigned long		index;
	struct list_head	entry;
};

/*
 * A post-processing bucket is, essentially, a size class, this defines
 * the range (in bytes) of pp-slots sizes in particular bucket.
 */
#define PP_BUCKET_SIZE_RANGE	64
#define NUM_PP_BUCKETS		((PAGE_SIZE / PP_BUCKET_SIZE_RANGE) + 1)

struct zram_pp_ctl {
	struct list_head	pp_buckets[NUM_PP_BUCKETS];
};

static struct zram_pp_ctl *init_pp_ctl(void)
{
	struct zram_pp_ctl *ctl;
	u32 idx;

	ctl = kmalloc(sizeof(*ctl), GFP_KERNEL);
	if (!ctl)
		return NULL;

	for (idx = 0; idx < NUM_PP_BUCKETS; idx++)
		INIT_LIST_HEAD(&ctl->pp_buckets[idx]);
	return ctl;
}

static void release_pp_slot(struct zram *zram, struct zram_pp_slot *pps)
{
	list_del_init(&pps->entry);

	zram_slot_lock(zram, pps->index);
	zram_clear_flag(zram, pps->index, ZRAM_PP_SLOT);
	zram_slot_unlock(zram, pps->index);

	kfree(pps);
}

static void release_pp_ctl(struct zram *zram, struct zram_pp_ctl *ctl)
{
	u32 idx;

	if (!ctl)
		return;

	for (idx = 0; idx < NUM_PP_BUCKETS; idx++) {
		while (!list_empty(&ctl->pp_buckets[idx])) {
			struct zram_pp_slot *pps;

			pps = list_first_entry(&ctl->pp_buckets[idx],
					       struct zram_pp_slot,
					       entry);
			release_pp_slot(zram, pps);
		}
	}

	kfree(ctl);
}

static void place_pp_slot(struct zram *zram, struct zram_pp_ctl *ctl,
			  struct zram_pp_slot *pps)
{
	u32 bid;

	bid = zram_get_obj_size(zram, pps->index) / PP_BUCKET_SIZE_RANGE;
	list_add(&pps->entry, &ctl->pp_buckets[bid]);

	zram_set_flag(zram, pps->index, ZRAM_PP_SLOT);
}

static struct zram_pp_slot *select_pp_slot(struct zram_pp_ctl *ctl)
{
	struct zram_pp_slot *pps = NULL;
	s32 idx = NUM_PP_BUCKETS - 1;

	/* The higher the bucket id the more optimal slot post-processing is */
	while (idx >= 0) {
		pps = list_first_entry_or_null(&ctl->pp_buckets[idx],
					       struct zram_pp_slot,
					       entry);
		if (pps)
			break;

		idx--;
	}
	return pps;
}
#endif

/*
 * Check if request is within bounds and aligned on zram logical blocks.
 */
static inline bool valid_io_request(struct zram *zram,
		sector_t start, unsigned int size)
{
	u64 end, bound;

	/* unaligned request */
	if (unlikely(start & (ZRAM_SECTOR_PER_LOGICAL_BLOCK - 1)))
		return false;
	if (unlikely(size & (ZRAM_LOGICAL_BLOCK_SIZE - 1)))
		return false;

	end = start + (size >> SECTOR_SHIFT);
	bound = zram->disksize >> SECTOR_SHIFT;
	/* out of range range */
	if (unlikely(start >= bound || end > bound || start > end))
		return false;

	/* I/O request is valid */
	return true;
}

static void update_position(u32 *index, int *offset, struct bio_vec *bvec)
{
	*index  += (*offset + bvec->bv_len) / PAGE_SIZE;
	*offset = (*offset + bvec->bv_len) % PAGE_SIZE;
}

static inline void update_used_max(struct zram *zram,
					const unsigned long pages)
{
	unsigned long old_max, cur_max;

	old_max = atomic_long_read(&zram->stats.max_used_pages);

	do {
		cur_max = old_max;
		if (pages > cur_max)
			old_max = atomic_long_cmpxchg(
				&zram->stats.max_used_pages, cur_max, pages);
	} while (old_max != cur_max);
}

static inline void zram_fill_page(void *ptr, unsigned long len,
					unsigned long value)
{
	WARN_ON_ONCE(!IS_ALIGNED(len, sizeof(unsigned long)));
	memset_l(ptr, value, len / sizeof(unsigned long));
}

static bool page_same_filled(void *ptr, unsigned long *element)
{
	unsigned long *page;
	unsigned long val;
	unsigned int pos, last_pos = PAGE_SIZE / sizeof(*page) - 1;

	page = (unsigned long *)ptr;
	val = page[0];

	if (val != page[last_pos])
		return false;

	for (pos = 1; pos < last_pos; pos++) {
		if (val != page[pos])
			return false;
	}

	*element = val;

	return true;
}

static ssize_t initstate_show(struct device *dev,
		struct device_attribute *attr, char *buf)
{
	u32 val;
	struct zram *zram = dev_to_zram(dev);

	down_read(&zram->init_lock);
	val = init_done(zram);
	up_read(&zram->init_lock);

	return scnprintf(buf, PAGE_SIZE, "%u\n", val);
}

static ssize_t disksize_show(struct device *dev,
		struct device_attribute *attr, char *buf)
{
	struct zram *zram = dev_to_zram(dev);

	return scnprintf(buf, PAGE_SIZE, "%llu\n", zram->disksize);
}

static ssize_t mem_limit_store(struct device *dev,
		struct device_attribute *attr, const char *buf, size_t len)
{
	u64 limit;
	char *tmp;
	struct zram *zram = dev_to_zram(dev);

	limit = memparse(buf, &tmp);
	if (buf == tmp) /* no chars parsed, invalid input */
		return -EINVAL;

	down_write(&zram->init_lock);
	zram->limit_pages = PAGE_ALIGN(limit) >> PAGE_SHIFT;
	up_write(&zram->init_lock);

	return len;
}

static ssize_t mem_used_max_store(struct device *dev,
		struct device_attribute *attr, const char *buf, size_t len)
{
	int err;
	unsigned long val;
	struct zram *zram = dev_to_zram(dev);

	err = kstrtoul(buf, 10, &val);
	if (err || val != 0)
		return -EINVAL;

	down_read(&zram->init_lock);
	if (init_done(zram)) {
		atomic_long_set(&zram->stats.max_used_pages,
				zs_get_total_pages(zram->mem_pool));
	}
	up_read(&zram->init_lock);

	return len;
}

/*
 * Mark all pages which are older than or equal to cutoff as IDLE.
 * Callers should hold the zram init lock in read mode
 */
static void mark_idle(struct zram *zram, ktime_t cutoff)
{
	int is_idle = 1;
	unsigned long nr_pages = zram->disksize >> PAGE_SHIFT;
	int index;

	for (index = 0; index < nr_pages; index++) {
		/*
		 * Do not mark ZRAM_SAME slots as ZRAM_IDLE, because no
		 * post-processing (recompress, writeback) happens to the
		 * ZRAM_SAME slot.
		 *
		 * And ZRAM_WB slots simply cannot be ZRAM_IDLE.
		 */
		zram_slot_lock(zram, index);
		if (!zram_allocated(zram, index) ||
		    zram_test_flag(zram, index, ZRAM_WB) ||
		    zram_test_flag(zram, index, ZRAM_SAME)) {
			zram_slot_unlock(zram, index);
			continue;
		}
#ifdef CONFIG_ZRAM_TRACK_ENTRY_ACTIME
		is_idle = !cutoff ||
			ktime_after(cutoff, zram->table[index].ac_time);
#endif
		if (is_idle)
			zram_set_flag(zram, index, ZRAM_IDLE);
		zram_slot_unlock(zram, index);
	}
}

static ssize_t idle_store(struct device *dev,
		struct device_attribute *attr, const char *buf, size_t len)
{
	struct zram *zram = dev_to_zram(dev);
	ktime_t cutoff_time = 0;
	ssize_t rv = -EINVAL;

	if (!sysfs_streq(buf, "all")) {
		/*
		 * If it did not parse as 'all' try to treat it as an integer when
		 * we have memory tracking enabled.
		 */
		u64 age_sec;

		if (IS_ENABLED(CONFIG_ZRAM_TRACK_ENTRY_ACTIME) && !kstrtoull(buf, 0, &age_sec))
			cutoff_time = ktime_sub(ktime_get_boottime(),
					ns_to_ktime(age_sec * NSEC_PER_SEC));
		else
			goto out;
	}

	down_read(&zram->init_lock);
	if (!init_done(zram))
		goto out_unlock;

	/* A cutoff_time of 0 marks everything as idle, this is the "all" behavior */
	mark_idle(zram, cutoff_time);
	rv = len;

out_unlock:
	up_read(&zram->init_lock);
out:
	return rv;
}

#ifdef CONFIG_ZRAM_WRITEBACK
static int read_from_zspool_raw(struct zram *zram, struct page *page,
				u32 index);

struct zram_wb_ctl {
	/* idle list is accessed only by the writeback task, no concurrency */
	struct list_head idle_reqs;
	/* done list is accessed concurrently, protected by done_lock */
	struct list_head done_reqs;
	wait_queue_head_t done_wait;
	spinlock_t done_lock;
	atomic_t num_inflight;
	struct rcu_head rcu;
};

struct zram_wb_req {
	unsigned long blk_idx;
	u32 index;
	struct page *page;
	struct zram_pp_slot *pps;
	struct bio_vec bio_vec;
	struct bio bio;

	struct list_head entry;
};

struct zram_rb_req {
	struct work_struct work;
	struct zram *zram;
	struct page *page;
	/* The read bio for backing device */
	struct bio *bio;
	unsigned long blk_idx;
	union {
		/* The original bio to complete (async read) */
		struct bio *parent;
		/* error status (sync read) */
		int error;
	};
	u32 index;
};

static ssize_t compressed_writeback_store(struct device *dev,
					  struct device_attribute *attr,
					  const char *buf, size_t len)
{
	struct zram *zram = dev_to_zram(dev);
	bool val;

	if (kstrtobool(buf, &val))
		return -EINVAL;

	down_write(&zram->init_lock);
	if (init_done(zram)) {
		up_write(&zram->init_lock);
		return -EBUSY;
	}

	zram->compressed_wb = val;
	up_write(&zram->init_lock);

	return len;
}

static ssize_t compressed_writeback_show(struct device *dev,
					 struct device_attribute *attr,
					 char *buf)
{
	bool val;
	struct zram *zram = dev_to_zram(dev);

	down_read(&zram->init_lock);
	val = zram->compressed_wb;
	up_read(&zram->init_lock);

	return scnprintf(buf, PAGE_SIZE, "%d\n", val);
}

static ssize_t writeback_limit_enable_store(struct device *dev,
					    struct device_attribute *attr,
					    const char *buf, size_t len)
{
	struct zram *zram = dev_to_zram(dev);
	u64 val;
	ssize_t ret = -EINVAL;

	if (kstrtoull(buf, 10, &val))
		return ret;

	down_write(&zram->init_lock);
	spin_lock(&zram->wb_limit_lock);
	zram->wb_limit_enable = val;
	spin_unlock(&zram->wb_limit_lock);
	up_write(&zram->init_lock);
	ret = len;

	return ret;
}

static ssize_t writeback_limit_enable_show(struct device *dev,
					   struct device_attribute *attr,
					   char *buf)
{
	bool val;
	struct zram *zram = dev_to_zram(dev);

	down_read(&zram->init_lock);
	spin_lock(&zram->wb_limit_lock);
	val = zram->wb_limit_enable;
	spin_unlock(&zram->wb_limit_lock);
	up_read(&zram->init_lock);

	return scnprintf(buf, PAGE_SIZE, "%d\n", val);
}

static ssize_t writeback_limit_store(struct device *dev,
				     struct device_attribute *attr,
				     const char *buf, size_t len)
{
	struct zram *zram = dev_to_zram(dev);
	u64 val;
	ssize_t ret = -EINVAL;

	if (kstrtoull(buf, 10, &val))
		return ret;

	down_write(&zram->init_lock);
	spin_lock(&zram->wb_limit_lock);
	zram->bd_wb_limit = val;
	spin_unlock(&zram->wb_limit_lock);
	up_write(&zram->init_lock);
	ret = len;

	return ret;
}

static ssize_t writeback_limit_show(struct device *dev,
				    struct device_attribute *attr, char *buf)
{
	u64 val;
	struct zram *zram = dev_to_zram(dev);

	down_read(&zram->init_lock);
	spin_lock(&zram->wb_limit_lock);
	val = zram->bd_wb_limit;
	spin_unlock(&zram->wb_limit_lock);
	up_read(&zram->init_lock);

	return scnprintf(buf, PAGE_SIZE, "%llu\n", val);
}

static ssize_t writeback_batch_size_store(struct device *dev,
					  struct device_attribute *attr,
					  const char *buf, size_t len)
{
	struct zram *zram = dev_to_zram(dev);
	u32 val;

	if (kstrtouint(buf, 10, &val))
		return -EINVAL;

	if (!val)
		return -EINVAL;

	down_write(&zram->init_lock);
	zram->wb_batch_size = val;
	up_write(&zram->init_lock);

	return len;
}

static ssize_t writeback_batch_size_show(struct device *dev,
					 struct device_attribute *attr,
					 char *buf)
{
	u32 val;
	struct zram *zram = dev_to_zram(dev);

	down_read(&zram->init_lock);
	val = zram->wb_batch_size;
	up_read(&zram->init_lock);

	return scnprintf(buf, PAGE_SIZE, "%u\n", val);
}

static void reset_bdev(struct zram *zram)
{
	struct block_device *bdev;

	if (!zram->backing_dev)
		return;

	bdev = zram->bdev;
	if (zram->old_block_size)
		set_blocksize(bdev, zram->old_block_size);
	blkdev_put(bdev, FMODE_READ|FMODE_WRITE|FMODE_EXCL);
	/* hope filp_close flush all of IO */
	filp_close(zram->backing_dev, NULL);
	zram->backing_dev = NULL;
	zram->old_block_size = 0;
	zram->bdev = NULL;
	zram->disk->fops = &zram_devops;
	kvfree(zram->bitmap);
	zram->bitmap = NULL;
}

static ssize_t backing_dev_show(struct device *dev,
		struct device_attribute *attr, char *buf)
{
	struct file *file;
	struct zram *zram = dev_to_zram(dev);
	char *p;
	ssize_t ret;

	down_read(&zram->init_lock);
	file = zram->backing_dev;
	if (!file) {
		memcpy(buf, "none\n", 5);
		up_read(&zram->init_lock);
		return 5;
	}

	p = file_path(file, buf, PAGE_SIZE - 1);
	if (IS_ERR(p)) {
		ret = PTR_ERR(p);
		goto out;
	}

	ret = strlen(p);
	memmove(buf, p, ret);
	buf[ret++] = '\n';
out:
	up_read(&zram->init_lock);
	return ret;
}

static ssize_t backing_dev_store(struct device *dev,
		struct device_attribute *attr, const char *buf, size_t len)
{
	char *file_name;
	size_t sz;
	struct file *backing_dev = NULL;
	struct inode *inode;
	struct address_space *mapping;
	unsigned int bitmap_sz, old_block_size = 0;
	unsigned long nr_pages, *bitmap = NULL;
	struct block_device *bdev = NULL;
	int err;
	struct zram *zram = dev_to_zram(dev);

	file_name = kmalloc(PATH_MAX, GFP_KERNEL);
	if (!file_name)
		return -ENOMEM;

	down_write(&zram->init_lock);
	if (init_done(zram)) {
		pr_info("Can't setup backing device for initialized device\n");
		err = -EBUSY;
		goto out;
	}

	strlcpy(file_name, buf, PATH_MAX);
	/* ignore trailing newline */
	sz = strlen(file_name);
	if (sz > 0 && file_name[sz - 1] == '\n')
		file_name[sz - 1] = 0x00;

	backing_dev = filp_open_block(file_name, O_RDWR|O_LARGEFILE, 0);
	if (IS_ERR(backing_dev)) {
		err = PTR_ERR(backing_dev);
		backing_dev = NULL;
		goto out;
	}

	mapping = backing_dev->f_mapping;
	inode = mapping->host;

	/* Support only block device in this moment */
	if (!S_ISBLK(inode->i_mode)) {
		err = -ENOTBLK;
		goto out;
	}

	bdev = blkdev_get_by_dev(inode->i_rdev,
			FMODE_READ | FMODE_WRITE | FMODE_EXCL, zram);
	if (IS_ERR(bdev)) {
		err = PTR_ERR(bdev);
		bdev = NULL;
		goto out;
	}

	nr_pages = i_size_read(inode) >> PAGE_SHIFT;
	/* Refuse to use zero sized device (also prevents self reference) */
	if (!nr_pages) {
		err = -EINVAL;
		goto out;
	}

	bitmap_sz = BITS_TO_LONGS(nr_pages) * sizeof(long);
	bitmap = kvzalloc(bitmap_sz, GFP_KERNEL);
	if (!bitmap) {
		err = -ENOMEM;
		goto out;
	}

	old_block_size = block_size(bdev);
	err = set_blocksize(bdev, PAGE_SIZE);
	if (err)
		goto out;

	reset_bdev(zram);

	zram->old_block_size = old_block_size;
	zram->bdev = bdev;
	zram->backing_dev = backing_dev;
	zram->bitmap = bitmap;
	zram->nr_pages = nr_pages;
	/*
	 * With writeback feature, zram does asynchronous IO so it's no longer
	 * synchronous device so let's remove synchronous io flag. Othewise,
	 * upper layer(e.g., swap) could wait IO completion rather than
	 * (submit and return), which will cause system sluggish.
	 * Furthermore, when the IO function returns(e.g., swap_readpage),
	 * upper layer expects IO was done so it could deallocate the page
	 * freely but in fact, IO is going on so finally could cause
	 * use-after-free when the IO is really done.
	 */
	zram->disk->fops = &zram_wb_devops;
	up_write(&zram->init_lock);

	pr_info("setup backing device %s\n", file_name);
	kfree(file_name);

	return len;
out:
	if (bitmap)
		kvfree(bitmap);

	if (bdev)
		blkdev_put(bdev, FMODE_READ | FMODE_WRITE | FMODE_EXCL);

	if (backing_dev)
		filp_close(backing_dev, NULL);

	up_write(&zram->init_lock);

	kfree(file_name);

	return err;
}

static unsigned long alloc_block_bdev(struct zram *zram)
{
	unsigned long blk_idx = 1;
retry:
	/* skip 0 bit to confuse zram.handle = 0 */
	blk_idx = find_next_zero_bit(zram->bitmap, zram->nr_pages, blk_idx);
	if (blk_idx == zram->nr_pages)
		return 0;

	if (test_and_set_bit(blk_idx, zram->bitmap))
		goto retry;

	atomic64_inc(&zram->stats.bd_count);
	return blk_idx;
}

static void free_block_bdev(struct zram *zram, unsigned long blk_idx)
{
	int was_set;

	was_set = test_and_clear_bit(blk_idx, zram->bitmap);
	WARN_ON_ONCE(!was_set);
	atomic64_dec(&zram->stats.bd_count);
}

static int decompress_bdev_page(struct zram *zram, struct page *page,
				u32 index, unsigned long blk_idx)
{
	struct zcomp_strm *zstrm;
	unsigned int size;
	int ret, prio;
	void *src;

	zram_slot_lock(zram, index);
	/* Since slot was unlocked we need to make sure it's still ZRAM_WB */
	if (!zram_test_flag(zram, index, ZRAM_WB) ||
	    zram_get_handle(zram, index) != blk_idx) {
		zram_slot_unlock(zram, index);
		/* We read some stale data, zero it out */
		src = kmap_atomic(page);
		memset(src, 0, PAGE_SIZE);
		kunmap_atomic(src);
		return -EIO;
	}

	if (zram_test_flag(zram, index, ZRAM_HUGE)) {
		zram_slot_unlock(zram, index);
		return 0;
	}

	size = zram_get_obj_size(zram, index);
	prio = zram_get_priority(zram, index);

	zstrm = zcomp_stream_get(zram->comps[prio]);
	src = kmap_atomic(page);
	ret = zcomp_decompress(zstrm, src, size, zstrm->buffer);
	if (!ret)
		memcpy(src, zstrm->buffer, PAGE_SIZE);
	kunmap_atomic(src);
	zcomp_stream_put(zram->comps[prio]);
	zram_slot_unlock(zram, index);

	return ret;
}

static void zram_deferred_decompress(struct work_struct *w)
{
	struct zram_rb_req *req = container_of(w, struct zram_rb_req, work);
	struct page *page = bio_first_page_all(req->bio);
	struct zram *zram = req->zram;
	int ret;

	ret = decompress_bdev_page(zram, page, req->index, req->blk_idx);
	flush_dcache_page(page);

	if (req->parent) {
		if (ret)
			req->parent->bi_status = BLK_STS_IOERR;
		/* Decrement parent's ->remaining */
		bio_endio(req->parent);
	} else {
		page_endio(page, false, ret);
	}
	bio_put(req->bio);
	kfree(req);
}

static void zram_async_read_endio(struct bio *bio)
{
	struct zram_rb_req *req = bio->bi_private;
	struct zram *zram = req->zram;

	if (bio->bi_status) {
		if (req->parent) {
			req->parent->bi_status = bio->bi_status;
			bio_endio(req->parent);
		} else {
			page_endio(bio_first_page_all(bio), false,
				   blk_status_to_errno(bio->bi_status));
		}
		bio_put(bio);
		kfree(req);
		return;
	}

	if (!zram->compressed_wb) {
		if (req->parent)
			bio_endio(req->parent);
		else
			page_endio(bio_first_page_all(bio), false, 0);
		bio_put(bio);
		kfree(req);
		return;
	}

	/*
	 * zram decompression requires a preemptible context for per-CPU
	 * crypto streams / workqueue offload.
	 */
	INIT_WORK(&req->work, zram_deferred_decompress);
	queue_work(system_highpri_wq, &req->work);
}

/*
 * Returns 1 if the submission is successful, or negative errno on failure.
 */
static int read_from_bdev_async(struct zram *zram, struct bio_vec *bvec,
				u32 index, unsigned long blk_idx,
				struct bio *parent)
{
	struct zram_rb_req *req;
	struct bio *bio;

	req = kmalloc(sizeof(*req), GFP_NOIO);
	if (!req)
		return -ENOMEM;

	bio = bio_alloc(GFP_NOIO, 1);
	if (!bio) {
		kfree(req);
		return -ENOMEM;
	}

	bio->bi_iter.bi_sector = blk_idx * (PAGE_SIZE >> 9);
	bio_set_dev(bio, zram->bdev);
	if (!bio_add_page(bio, bvec->bv_page, bvec->bv_len, bvec->bv_offset)) {
		bio_put(bio);
		kfree(req);
		return -EIO;
	}

	req->zram = zram;
	req->index = index;
	req->blk_idx = blk_idx;
	req->bio = bio;
	req->parent = parent;

	bio->bi_opf = parent ? parent->bi_opf : REQ_OP_READ;
	bio->bi_private = req;
	bio->bi_end_io = zram_async_read_endio;

	if (parent)
		bio_inc_remaining(parent);
	submit_bio(bio);
	return 1;
}

#define PAGE_WB_SIG "page_index="

#define PAGE_WRITEBACK			0
#define HUGE_WRITEBACK			(1<<0)
#define IDLE_WRITEBACK			(1<<1)
#define INCOMPRESSIBLE_WRITEBACK	(1<<2)

static int scan_slots_for_writeback(struct zram *zram, u32 mode,
				    unsigned long nr_pages,
				    unsigned long index,
				    struct zram_pp_ctl *ctl)
{
	struct zram_pp_slot *pps = NULL;

	for (; nr_pages != 0; index++, nr_pages--) {
		if (!pps) {
			pps = kmalloc(sizeof(*pps), GFP_NOIO | __GFP_NOWARN);
			if (!pps)
				break;
			INIT_LIST_HEAD(&pps->entry);
		}

		zram_slot_lock(zram, index);
		if (!zram_allocated(zram, index))
			goto next;

		if (zram_test_flag(zram, index, ZRAM_WB) ||
		    zram_test_flag(zram, index, ZRAM_SAME) ||
		    zram_test_flag(zram, index, ZRAM_PP_SLOT))
			goto next;

		if (mode & IDLE_WRITEBACK &&
		    !zram_test_flag(zram, index, ZRAM_IDLE))
			goto next;
		if (mode & HUGE_WRITEBACK &&
		    !zram_test_flag(zram, index, ZRAM_HUGE))
			goto next;
		if (mode & INCOMPRESSIBLE_WRITEBACK &&
		    !zram_test_flag(zram, index, ZRAM_INCOMPRESSIBLE))
			goto next;

		pps->index = index;
		place_pp_slot(zram, ctl, pps);
		pps = NULL;
next:
		zram_slot_unlock(zram, index);
	}

	kfree(pps);
	return 0;
}

static void release_wb_req(struct zram_wb_req *req)
{
	__free_page(req->page);
	kfree(req);
}

static void release_wb_ctl(struct zram_wb_ctl *wb_ctl)
{
	if (!wb_ctl)
		return;

	/* We should never have inflight requests at this point */
	WARN_ON(atomic_read(&wb_ctl->num_inflight));
	WARN_ON(!list_empty(&wb_ctl->done_reqs));

	while (!list_empty(&wb_ctl->idle_reqs)) {
		struct zram_wb_req *req;

		req = list_first_entry(&wb_ctl->idle_reqs,
				       struct zram_wb_req, entry);
		list_del(&req->entry);
		release_wb_req(req);
	}

	kfree_rcu(wb_ctl, rcu);
}

static struct zram_wb_ctl *init_wb_ctl(struct zram *zram)
{
	struct zram_wb_ctl *wb_ctl;
	u32 i;

	wb_ctl = kmalloc(sizeof(*wb_ctl), GFP_KERNEL);
	if (!wb_ctl)
		return NULL;

	INIT_LIST_HEAD(&wb_ctl->idle_reqs);
	INIT_LIST_HEAD(&wb_ctl->done_reqs);
	atomic_set(&wb_ctl->num_inflight, 0);
	init_waitqueue_head(&wb_ctl->done_wait);
	spin_lock_init(&wb_ctl->done_lock);

	for (i = 0; i < zram->wb_batch_size; i++) {
		struct zram_wb_req *req;

		/*
		 * This is fatal condition only if we couldn't allocate
		 * any requests at all. Otherwise we just work with the
		 * requests that we have successfully allocated, so that
		 * writeback can still proceed, even if there is only one
		 * request on the idle list.
		 */
		req = kzalloc(sizeof(*req), GFP_KERNEL | __GFP_NOWARN);
		if (!req)
			break;

		req->page = alloc_page(GFP_KERNEL | __GFP_NOWARN);
		if (!req->page) {
			kfree(req);
			break;
		}

		list_add(&req->entry, &wb_ctl->idle_reqs);
	}

	/* We couldn't allocate any requests, so writeback is not possible */
	if (list_empty(&wb_ctl->idle_reqs))
		goto release_wb_ctl;

	return wb_ctl;

release_wb_ctl:
	release_wb_ctl(wb_ctl);
	return NULL;
}

static void zram_account_writeback_rollback(struct zram *zram)
{
	spin_lock(&zram->wb_limit_lock);
	if (zram->wb_limit_enable)
		zram->bd_wb_limit += 1UL << (PAGE_SHIFT - 12);
	spin_unlock(&zram->wb_limit_lock);
}

static void zram_account_writeback_submit(struct zram *zram)
{
	spin_lock(&zram->wb_limit_lock);
	if (zram->wb_limit_enable && zram->bd_wb_limit > 0)
		zram->bd_wb_limit -= 1UL << (PAGE_SHIFT - 12);
	spin_unlock(&zram->wb_limit_lock);
}

static int zram_writeback_complete(struct zram *zram, struct zram_wb_req *req,
				   u64 *written_bytes)
{
	u32 index = req->pps->index;
	int err;

	err = blk_status_to_errno(req->bio.bi_status);
	if (err) {
		/*
		 * Failed wb requests should not be accounted in wb_limit
		 * (if enabled).
		 */
		zram_account_writeback_rollback(zram);
		free_block_bdev(zram, req->blk_idx);
		return err;
	}

	atomic64_inc(&zram->stats.bd_writes);
	zram_slot_lock(zram, index);
	/*
	 * We release slot lock during writeback so slot can change under us:
	 * slot_free() or slot_free() and zram_write_page(). In both cases
	 * slot loses ZRAM_PP_SLOT flag.
	 */
	if (!zram_test_flag(zram, index, ZRAM_PP_SLOT)) {
		free_block_bdev(zram, req->blk_idx);
		goto out;
	}

	zram_clear_flag(zram, index, ZRAM_IDLE);
	if (zram_test_flag(zram, index, ZRAM_HUGE))
		atomic64_dec(&zram->stats.huge_pages);
	atomic64_sub(zram_get_obj_size(zram, index),
		     &zram->stats.compr_data_size);
	zs_free(zram->mem_pool, zram_get_handle(zram, index));
	zram_set_handle(zram, index, req->blk_idx);
	zram_set_flag(zram, index, ZRAM_WB);
	if (written_bytes)
		*written_bytes += PAGE_SIZE;

out:
	zram_slot_unlock(zram, index);
	return 0;
}

static void zram_writeback_endio(struct bio *bio)
{
	struct zram_wb_req *req = container_of(bio, struct zram_wb_req, bio);
	struct zram_wb_ctl *wb_ctl = bio->bi_private;
	unsigned long flags;

	rcu_read_lock();
	spin_lock_irqsave(&wb_ctl->done_lock, flags);
	list_add(&req->entry, &wb_ctl->done_reqs);
	spin_unlock_irqrestore(&wb_ctl->done_lock, flags);

	wake_up(&wb_ctl->done_wait);
	rcu_read_unlock();
}

static void zram_submit_wb_request(struct zram *zram,
				   struct zram_wb_ctl *wb_ctl,
				   struct zram_wb_req *req)
{
	/*
	 * wb_limit (if enabled) should be adjusted before submission,
	 * so that we don't over-submit.
	 */
	zram_account_writeback_submit(zram);
	atomic_inc(&wb_ctl->num_inflight);
	req->bio.bi_private = wb_ctl;
	submit_bio(&req->bio);
}

static int zram_complete_done_reqs(struct zram *zram,
				   struct zram_wb_ctl *wb_ctl,
				   u64 *written_bytes)
{
	struct zram_wb_req *req;
	unsigned long flags;
	int ret = 0, err;

	while (atomic_read(&wb_ctl->num_inflight) > 0) {
		spin_lock_irqsave(&wb_ctl->done_lock, flags);
		req = list_first_entry_or_null(&wb_ctl->done_reqs,
					       struct zram_wb_req, entry);
		if (req)
			list_del(&req->entry);
		spin_unlock_irqrestore(&wb_ctl->done_lock, flags);

		/* ->num_inflight > 0 doesn't mean we have done requests */
		if (!req)
			break;

		err = zram_writeback_complete(zram, req, written_bytes);
		if (err)
			ret = err;

		atomic_dec(&wb_ctl->num_inflight);
		release_pp_slot(zram, req->pps);
		req->pps = NULL;

		list_add(&req->entry, &wb_ctl->idle_reqs);
	}

	return ret;
}

static struct zram_wb_req *zram_select_idle_req(struct zram_wb_ctl *wb_ctl)
{
	struct zram_wb_req *req;

	req = list_first_entry_or_null(&wb_ctl->idle_reqs,
				       struct zram_wb_req, entry);
	if (req)
		list_del(&req->entry);
	return req;
}

static int zram_writeback_slots(struct zram *zram,
				struct zram_pp_ctl *ctl,
				struct zram_wb_ctl *wb_ctl,
				u64 *written_bytes)
{
	struct zram_wb_req *req = NULL;
	unsigned long blk_idx = 0;
	struct zram_pp_slot *pps;
	int ret = 0, err = 0;
	u32 index = 0;

	while ((pps = select_pp_slot(ctl))) {
		if (written_bytes && fatal_signal_pending(current)) {
			ret = -EINTR;
			break;
		}

		spin_lock(&zram->wb_limit_lock);
		if (zram->wb_limit_enable && !zram->bd_wb_limit) {
			spin_unlock(&zram->wb_limit_lock);
			ret = -EIO;
			break;
		}
		spin_unlock(&zram->wb_limit_lock);

		while (!req) {
			req = zram_select_idle_req(wb_ctl);
			if (req)
				break;

			wait_event(wb_ctl->done_wait,
				   !list_empty(&wb_ctl->done_reqs));

			err = zram_complete_done_reqs(zram, wb_ctl,
						      written_bytes);
			/*
			 * BIO errors are not fatal, we continue and simply
			 * attempt to writeback the remaining objects (pages).
			 * At the same time we need to signal user-space that
			 * some writes (at least one, but also could be all of
			 * them) were not successful and we do so by returning
			 * the most recent BIO error.
			 */
			if (err)
				ret = err;
		}

		if (!blk_idx) {
			blk_idx = alloc_block_bdev(zram);
			if (!blk_idx) {
				ret = -ENOSPC;
				break;
			}
		}

		index = pps->index;
		zram_slot_lock(zram, index);
		/*
		 * scan_slots() sets ZRAM_PP_SLOT and releases slot lock, so
		 * slots can change in the meantime. If slots are accessed or
		 * freed they lose ZRAM_PP_SLOT flag and hence we don't
		 * post-process them.
		 */
		if (!zram_test_flag(zram, index, ZRAM_PP_SLOT))
			goto next;
		if (zram->compressed_wb)
			err = read_from_zspool_raw(zram, req->page, index);
		else
			err = zram_read_from_zspool(zram, req->page, index);
		if (err)
			goto next;
		zram_slot_unlock(zram, index);

		/*
		 * From now on pp-slot is owned by the req, remove it from
		 * its pp bucket.
		 */
		list_del_init(&pps->entry);

		req->blk_idx = blk_idx;
		req->pps = pps;
		bio_init(&req->bio, &req->bio_vec, 1);
		bio_set_dev(&req->bio, zram->bdev);
		req->bio.bi_iter.bi_sector = req->blk_idx * (PAGE_SIZE >> 9);
		req->bio.bi_opf = REQ_OP_WRITE;
		req->bio.bi_end_io = zram_writeback_endio;
		bio_add_page(&req->bio, req->page, PAGE_SIZE, 0);

		zram_submit_wb_request(zram, wb_ctl, req);
		blk_idx = 0;
		req = NULL;
		cond_resched();
		continue;

next:
		zram_slot_unlock(zram, index);
		release_pp_slot(zram, pps);
	}

	/*
	 * Selected idle req, but never submitted it due to some error or
	 * wb limit.
	 */
	if (req)
		release_wb_req(req);

	if (blk_idx)
		free_block_bdev(zram, blk_idx);

	while (atomic_read(&wb_ctl->num_inflight) > 0) {
		wait_event(wb_ctl->done_wait, !list_empty(&wb_ctl->done_reqs));
		err = zram_complete_done_reqs(zram, wb_ctl, written_bytes);
		if (err)
			ret = err;
	}

	return ret;
}

static ssize_t writeback_store(struct device *dev,
		struct device_attribute *attr, const char *buf, size_t len)
{
	struct zram *zram = dev_to_zram(dev);
	unsigned long nr_pages;
	struct zram_pp_ctl *pp_ctl = NULL;
	struct zram_wb_ctl *wb_ctl = NULL;
	unsigned long index = 0;
	ssize_t ret = len;
	int mode, err;

	if (sysfs_streq(buf, "idle"))
		mode = IDLE_WRITEBACK;
	else if (sysfs_streq(buf, "huge"))
		mode = HUGE_WRITEBACK;
	else if (sysfs_streq(buf, "huge_idle"))
		mode = IDLE_WRITEBACK | HUGE_WRITEBACK;
	else if (sysfs_streq(buf, "incompressible"))
		mode = INCOMPRESSIBLE_WRITEBACK;
	else {
		if (strncmp(buf, PAGE_WB_SIG, sizeof(PAGE_WB_SIG) - 1))
			return -EINVAL;

		if (kstrtoul(buf + sizeof(PAGE_WB_SIG) - 1, 10, &index))
			return -EINVAL;

		mode = PAGE_WRITEBACK;
	}

	down_read(&zram->init_lock);
	if (!init_done(zram)) {
		ret = -EINVAL;
		goto release_init_lock;
	}

	if (!zram->backing_dev) {
		ret = -ENODEV;
		goto release_init_lock;
	}

	nr_pages = zram->disksize >> PAGE_SHIFT;
	if (mode == PAGE_WRITEBACK) {
		if (index >= nr_pages) {
			ret = -EINVAL;
			goto release_init_lock;
		}
		nr_pages = 1;
	}

	pp_ctl = init_pp_ctl();
	if (!pp_ctl) {
		ret = -ENOMEM;
		goto release_init_lock;
	}

	wb_ctl = init_wb_ctl(zram);
	if (!wb_ctl) {
		ret = -ENOMEM;
		goto release_init_lock;
	}

	scan_slots_for_writeback(zram, mode, nr_pages, index, pp_ctl);

	err = zram_writeback_slots(zram, pp_ctl, wb_ctl, NULL);
	if (err)
		ret = err;

release_init_lock:
	release_pp_ctl(zram, pp_ctl);
	release_wb_ctl(wb_ctl);
	up_read(&zram->init_lock);

	return ret;
}

#if PAGE_SIZE != 4096
static void zram_sync_read(struct work_struct *w)
{
	struct zram_rb_req *req = container_of(w, struct zram_rb_req, work);
	struct bio_vec bv;
	struct bio bio;

	bio_init(&bio, &bv, 1);
	bio_set_dev(&bio, req->zram->bdev);
	bio.bi_iter.bi_sector = req->blk_idx * (PAGE_SIZE >> 9);
	bio.bi_opf = REQ_OP_READ;
	bio_add_page(&bio, req->page, PAGE_SIZE, 0);
	req->error = submit_bio_wait(&bio);
}

/*
 * Block layer want one ->submit_bio to be active at a time, so if we use
 * chained IO with parent IO in same context, it's a deadlock. To avoid that,
 * use a worker thread context.
 */
static int read_from_bdev_sync(struct zram *zram, struct bio_vec *bvec,
			       u32 index, unsigned long blk_idx)
{
	struct zram_rb_req req;

	req.page = bvec->bv_page;
	req.zram = zram;
	req.blk_idx = blk_idx;

	INIT_WORK_ONSTACK(&req.work, zram_sync_read);
	queue_work(system_unbound_wq, &req.work);
	flush_work(&req.work);
	destroy_work_on_stack(&req.work);

	if (req.error || !zram->compressed_wb)
		return req.error;

	return decompress_bdev_page(zram, bvec->bv_page, index, blk_idx);
}
#else
static int read_from_bdev_sync(struct zram *zram, struct bio_vec *bvec,
			       u32 index, unsigned long blk_idx)
{
	WARN_ON(1);
	return -EIO;
}
#endif

static int read_from_bdev(struct zram *zram, struct bio_vec *bvec,
			  u32 index, unsigned long blk_idx,
			  struct bio *parent, bool sync)
{
	atomic64_inc(&zram->stats.bd_reads);
	if (sync)
		return read_from_bdev_sync(zram, bvec, index, blk_idx);
	else
		return read_from_bdev_async(zram, bvec, index, blk_idx, parent);
}
#else
static inline void reset_bdev(struct zram *zram) {};
static int read_from_bdev(struct zram *zram, struct bio_vec *bvec,
			  u32 index, unsigned long blk_idx,
			  struct bio *parent, bool sync)
{
	return -EIO;
}

static void free_block_bdev(struct zram *zram, unsigned long blk_idx) {};
#endif

static void zram_accessed(struct zram *zram, u32 index)
{
	zram_clear_flag(zram, index, ZRAM_IDLE);
	zram_clear_flag(zram, index, ZRAM_PP_SLOT);
#ifdef CONFIG_ZRAM_TRACK_ENTRY_ACTIME
	zram->table[index].ac_time = ktime_get_boottime();
#endif
}

#ifdef CONFIG_ZRAM_MEMORY_TRACKING

static struct dentry *zram_debugfs_root;

static void zram_debugfs_create(void)
{
	zram_debugfs_root = debugfs_create_dir("zram", NULL);
}

static void zram_debugfs_destroy(void)
{
	debugfs_remove_recursive(zram_debugfs_root);
}

static ssize_t read_block_state(struct file *file, char __user *buf,
				size_t count, loff_t *ppos)
{
	char *kbuf;
	ssize_t index, written = 0;
	struct zram *zram = file->private_data;
	unsigned long nr_pages = zram->disksize >> PAGE_SHIFT;
	struct timespec64 ts;

	kbuf = kvmalloc(count, GFP_KERNEL);
	if (!kbuf)
		return -ENOMEM;

	down_read(&zram->init_lock);
	if (!init_done(zram)) {
		up_read(&zram->init_lock);
		kvfree(kbuf);
		return -EINVAL;
	}

	for (index = *ppos; index < nr_pages; index++) {
		int copied;

		zram_slot_lock(zram, index);
		if (!zram_allocated(zram, index))
			goto next;

		ts = ktime_to_timespec64(zram->table[index].ac_time);
		copied = snprintf(kbuf + written, count,
			"%12zd %12lld.%06lu %c%c%c%c%c%c\n",
			index, (s64)ts.tv_sec,
			ts.tv_nsec / NSEC_PER_USEC,
			zram_test_flag(zram, index, ZRAM_SAME) ? 's' : '.',
			zram_test_flag(zram, index, ZRAM_WB) ? 'w' : '.',
			zram_test_flag(zram, index, ZRAM_HUGE) ? 'h' : '.',
			zram_test_flag(zram, index, ZRAM_IDLE) ? 'i' : '.',
			zram_get_priority(zram, index) ? 'r' : '.',
			zram_test_flag(zram, index,
				       ZRAM_INCOMPRESSIBLE) ? 'n' : '.');

		if (count <= copied) {
			zram_slot_unlock(zram, index);
			break;
		}
		written += copied;
		count -= copied;
next:
		zram_slot_unlock(zram, index);
		*ppos += 1;
	}

	up_read(&zram->init_lock);
	if (copy_to_user(buf, kbuf, written))
		written = -EFAULT;
	kvfree(kbuf);

	return written;
}

static const struct file_operations proc_zram_block_state_op = {
	.open = simple_open,
	.read = read_block_state,
	.llseek = default_llseek,
};

static void zram_debugfs_register(struct zram *zram)
{
	if (!zram_debugfs_root)
		return;

	zram->debugfs_dir = debugfs_create_dir(zram->disk->disk_name,
						zram_debugfs_root);
	debugfs_create_file("block_state", 0400, zram->debugfs_dir,
				zram, &proc_zram_block_state_op);
}

static void zram_debugfs_unregister(struct zram *zram)
{
	debugfs_remove_recursive(zram->debugfs_dir);
}
#else
static void zram_debugfs_create(void) {};
static void zram_debugfs_destroy(void) {};
static void zram_debugfs_register(struct zram *zram) {};
static void zram_debugfs_unregister(struct zram *zram) {};
#endif

/*
 * We switched to per-cpu streams and this attr is not needed anymore.
 * However, we will keep it around for some time, because:
 * a) we may revert per-cpu streams in the future
 * b) it's visible to user space and we need to follow our 2 years
 *    retirement rule; but we already have a number of 'soon to be
 *    altered' attrs, so max_comp_streams need to wait for the next
 *    layoff cycle.
 */
static ssize_t max_comp_streams_show(struct device *dev,
		struct device_attribute *attr, char *buf)
{
	return scnprintf(buf, PAGE_SIZE, "%d\n", num_online_cpus());
}

static ssize_t max_comp_streams_store(struct device *dev,
		struct device_attribute *attr, const char *buf, size_t len)
{
	return len;
}

static void comp_algorithm_set(struct zram *zram, u32 prio, const char *alg)
{
	/* Do not free statically defined compression algorithms */
	if (zram->comp_algs[prio] != default_compressor)
		kfree(zram->comp_algs[prio]);

	zram->comp_algs[prio] = alg;
}

static ssize_t __comp_algorithm_show(struct zram *zram, u32 prio, char *buf)
{
	ssize_t sz;

	down_read(&zram->init_lock);
	sz = zcomp_available_show(zram->comp_algs[prio], buf);
	up_read(&zram->init_lock);

	return sz;
}

static int __comp_algorithm_store(struct zram *zram, u32 prio, const char *buf)
{
	char *compressor;
	size_t sz;

	sz = strlen(buf);
	if (sz >= CRYPTO_MAX_ALG_NAME)
		return -E2BIG;

	compressor = kstrdup(buf, GFP_KERNEL);
	if (!compressor)
		return -ENOMEM;

	/* ignore trailing newline */
	if (sz > 0 && compressor[sz - 1] == '\n')
		compressor[sz - 1] = 0x00;

	if (!zcomp_available_algorithm(compressor)) {
		kfree(compressor);
		return -EINVAL;
	}

	down_write(&zram->init_lock);
	if (init_done(zram)) {
		up_write(&zram->init_lock);
		kfree(compressor);
		pr_info("Can't change algorithm for initialized device\n");
		return -EBUSY;
	}

	comp_algorithm_set(zram, prio, compressor);
	up_write(&zram->init_lock);
	return 0;
}

static ssize_t comp_algorithm_show(struct device *dev,
				   struct device_attribute *attr,
				   char *buf)
{
	struct zram *zram = dev_to_zram(dev);

	return __comp_algorithm_show(zram, ZRAM_PRIMARY_COMP, buf);
}

static ssize_t comp_algorithm_store(struct device *dev,
				    struct device_attribute *attr,
				    const char *buf,
				    size_t len)
{
	struct zram *zram = dev_to_zram(dev);
	int ret;

	ret = __comp_algorithm_store(zram, ZRAM_PRIMARY_COMP, buf);
	return ret ? ret : len;
}

#ifdef CONFIG_ZRAM_MULTI_COMP
static ssize_t recomp_algorithm_show(struct device *dev,
				     struct device_attribute *attr,
				     char *buf)
{
	struct zram *zram = dev_to_zram(dev);
	ssize_t sz = 0;
	u32 prio;

	for (prio = ZRAM_SECONDARY_COMP; prio < ZRAM_MAX_COMPS; prio++) {
		if (!zram->comp_algs[prio])
			continue;

		sz += scnprintf(buf + sz, PAGE_SIZE - sz - 2, "#%d: ", prio);
		sz += __comp_algorithm_show(zram, prio, buf + sz);
	}

	return sz;
}

static ssize_t recomp_algorithm_store(struct device *dev,
				      struct device_attribute *attr,
				      const char *buf,
				      size_t len)
{
	struct zram *zram = dev_to_zram(dev);
	int prio = ZRAM_SECONDARY_COMP;
	char *args, *param, *val;
	char *alg = NULL;
	int ret;

	args = skip_spaces(buf);
	while (*args) {
		args = next_arg(args, &param, &val);

		if (!val || !*val)
			return -EINVAL;

		if (!strcmp(param, "algo")) {
			alg = val;
			continue;
		}

		if (!strcmp(param, "priority")) {
			ret = kstrtoint(val, 10, &prio);
			if (ret)
				return ret;
			continue;
		}
	}

	if (!alg)
		return -EINVAL;

	if (prio < ZRAM_SECONDARY_COMP || prio >= ZRAM_MAX_COMPS)
		return -EINVAL;

	ret = __comp_algorithm_store(zram, prio, alg);
	return ret ? ret : len;
}
#endif

static ssize_t compact_store(struct device *dev,
		struct device_attribute *attr, const char *buf, size_t len)
{
	struct zram *zram = dev_to_zram(dev);

	down_read(&zram->init_lock);
	if (!init_done(zram)) {
		up_read(&zram->init_lock);
		return -EINVAL;
	}

	zs_compact(zram->mem_pool);
	up_read(&zram->init_lock);

	return len;
}

static ssize_t io_stat_show(struct device *dev,
		struct device_attribute *attr, char *buf)
{
	struct zram *zram = dev_to_zram(dev);
	ssize_t ret;

	down_read(&zram->init_lock);
	ret = scnprintf(buf, PAGE_SIZE,
			"%8llu %8llu %8llu %8llu\n",
			(u64)atomic64_read(&zram->stats.failed_reads),
			(u64)atomic64_read(&zram->stats.failed_writes),
			(u64)atomic64_read(&zram->stats.invalid_io),
			(u64)atomic64_read(&zram->stats.notify_free));
	up_read(&zram->init_lock);

	return ret;
}

static ssize_t mm_stat_show(struct device *dev,
		struct device_attribute *attr, char *buf)
{
	struct zram *zram = dev_to_zram(dev);
	struct zs_pool_stats pool_stats;
	u64 orig_size, mem_used = 0;
	long max_used;
	ssize_t ret;

	memset(&pool_stats, 0x00, sizeof(struct zs_pool_stats));

	down_read(&zram->init_lock);
	if (init_done(zram)) {
		mem_used = zs_get_total_pages(zram->mem_pool);
		zs_pool_stats(zram->mem_pool, &pool_stats);
	}

	orig_size = atomic64_read(&zram->stats.pages_stored);
	max_used = atomic_long_read(&zram->stats.max_used_pages);

	ret = scnprintf(buf, PAGE_SIZE,
			"%8llu %8llu %8llu %8lu %8ld %8llu %8lu %8llu\n",
			orig_size << PAGE_SHIFT,
			(u64)atomic64_read(&zram->stats.compr_data_size),
			mem_used << PAGE_SHIFT,
			zram->limit_pages << PAGE_SHIFT,
			max_used << PAGE_SHIFT,
			(u64)atomic64_read(&zram->stats.same_pages),
			atomic_long_read(&pool_stats.pages_compacted),
			(u64)atomic64_read(&zram->stats.huge_pages));
	up_read(&zram->init_lock);

	return ret;
}

#ifdef CONFIG_ZRAM_WRITEBACK
#define FOUR_K(x) ((x) * (1 << (PAGE_SHIFT - 12)))
static ssize_t bd_stat_show(struct device *dev,
		struct device_attribute *attr, char *buf)
{
	struct zram *zram = dev_to_zram(dev);
	ssize_t ret;

	down_read(&zram->init_lock);
	ret = scnprintf(buf, PAGE_SIZE,
		"%8llu %8llu %8llu\n",
			FOUR_K((u64)atomic64_read(&zram->stats.bd_count)),
			FOUR_K((u64)atomic64_read(&zram->stats.bd_reads)),
			FOUR_K((u64)atomic64_read(&zram->stats.bd_writes)));
	up_read(&zram->init_lock);

	return ret;
}
#endif

static ssize_t debug_stat_show(struct device *dev,
		struct device_attribute *attr, char *buf)
{
	int version = 1;
	struct zram *zram = dev_to_zram(dev);
	ssize_t ret;

	down_read(&zram->init_lock);
	ret = scnprintf(buf, PAGE_SIZE,
			"version: %d\n%8llu %8llu\n",
			version,
			(u64)atomic64_read(&zram->stats.writestall),
			(u64)atomic64_read(&zram->stats.miss_free));
	up_read(&zram->init_lock);

	return ret;
}

static DEVICE_ATTR_RO(io_stat);
static DEVICE_ATTR_RO(mm_stat);
#ifdef CONFIG_ZRAM_WRITEBACK
static DEVICE_ATTR_RO(bd_stat);
#endif
static DEVICE_ATTR_RO(debug_stat);

static void zram_meta_free(struct zram *zram, u64 disksize)
{
	size_t num_pages = disksize >> PAGE_SHIFT;
	size_t index;

	/* Free all pages that are still in this zram device */
	for (index = 0; index < num_pages; index++)
		zram_free_page(zram, index);

	zs_destroy_pool(zram->mem_pool);
	vfree(zram->table);
}

static bool zram_meta_alloc(struct zram *zram, u64 disksize)
{
	size_t num_pages;

	num_pages = disksize >> PAGE_SHIFT;
	zram->table = vzalloc(array_size(num_pages, sizeof(*zram->table)));
	if (!zram->table)
		return false;

	zram->mem_pool = zs_create_pool(zram->disk->disk_name);
	if (!zram->mem_pool) {
		vfree(zram->table);
		return false;
	}

	if (!huge_class_size)
		huge_class_size = zs_huge_class_size(zram->mem_pool);
	return true;
}

/*
 * To protect concurrent access to the same index entry,
 * caller should hold this table index entry's bit_spinlock to
 * indicate this index entry is accessing.
 */
static void zram_free_page(struct zram *zram, size_t index)
{
	unsigned long handle;

#ifdef CONFIG_ZRAM_TRACK_ENTRY_ACTIME
	zram->table[index].ac_time = 0;
#endif
	if (zram_test_flag(zram, index, ZRAM_IDLE))
		zram_clear_flag(zram, index, ZRAM_IDLE);

	if (zram_test_flag(zram, index, ZRAM_HUGE)) {
		/*
		 * Writeback completion decrements ->huge_pages but keeps
		 * ZRAM_HUGE flag for deferred decompression path.
		 */
		if (!zram_test_flag(zram, index, ZRAM_WB))
			atomic64_dec(&zram->stats.huge_pages);
		zram_clear_flag(zram, index, ZRAM_HUGE);
	}

	if (zram_test_flag(zram, index, ZRAM_INCOMPRESSIBLE))
		zram_clear_flag(zram, index, ZRAM_INCOMPRESSIBLE);

	zram_set_priority(zram, index, 0);
	zram_clear_flag(zram, index, ZRAM_PP_SLOT);

	if (zram_test_flag(zram, index, ZRAM_WB)) {
		zram_clear_flag(zram, index, ZRAM_WB);
		free_block_bdev(zram, zram_get_element(zram, index));
		goto out;
	}

	/*
	 * No memory is allocated for same element filled pages.
	 * Simply clear same page flag.
	 */
	if (zram_test_flag(zram, index, ZRAM_SAME)) {
		zram_clear_flag(zram, index, ZRAM_SAME);
		atomic64_dec(&zram->stats.same_pages);
		goto out;
	}

	handle = zram_get_handle(zram, index);
	if (!handle)
		return;

	zs_free(zram->mem_pool, handle);

	atomic64_sub(zram_get_obj_size(zram, index),
			&zram->stats.compr_data_size);
out:
	atomic64_dec(&zram->stats.pages_stored);
	zram_set_handle(zram, index, 0);
	zram_set_obj_size(zram, index, 0);
	WARN_ON_ONCE(zram->table[index].flags & ~(1UL << ZRAM_LOCK));
}

/*
 * Reads a page from the writeback devices. Corresponding ZRAM slot
 * should be unlocked.
 */
static int zram_bvec_read_from_bdev(struct zram *zram, struct page *page,
				    u32 index, unsigned long blk_idx,
				    struct bio *bio, bool partial_io)
{
	struct bio_vec bvec = {
		.bv_page = page,
		.bv_len = PAGE_SIZE,
		.bv_offset = 0,
	};

	return read_from_bdev(zram, &bvec, index, blk_idx, bio, partial_io);
}

#ifdef CONFIG_ZRAM_WRITEBACK
/*
 * Reads raw (still compressed) object bytes from zspool into @page and
 * zero-fills any trailing bytes to prevent infoleaks on backing_dev.
 * Corresponding ZRAM slot should be locked.
 */
static int read_from_zspool_raw(struct zram *zram, struct page *page, u32 index)
{
	unsigned long handle;
	unsigned int size;
	void *src, *dst;

	handle = zram_get_handle(zram, index);
	size = zram_get_obj_size(zram, index);

	src = zs_map_object(zram->mem_pool, handle, ZS_MM_RO);
	dst = kmap_atomic(page);
	memcpy(dst, src, size);
	if (size < PAGE_SIZE)
		memset(dst + size, 0, PAGE_SIZE - size);
	kunmap_atomic(dst);
	zs_unmap_object(zram->mem_pool, handle);

	return 0;
}
#endif

/*
 * Reads (decompresses if needed) a page from zspool (zsmalloc).
 * Corresponding ZRAM slot should be locked.
 */
static int zram_read_from_zspool(struct zram *zram, struct page *page,
				 u32 index)
{
	struct zcomp_strm *zstrm;
	unsigned long handle;
	unsigned int size;
	void *src, *dst;
	u32 prio;
	int ret;

	handle = zram_get_handle(zram, index);
	if (!handle || zram_test_flag(zram, index, ZRAM_SAME)) {
		unsigned long value;
		void *mem;

		value = handle ? zram_get_element(zram, index) : 0;
		mem = kmap_atomic(page);
		zram_fill_page(mem, PAGE_SIZE, value);
		kunmap_atomic(mem);
		return 0;
	}

	size = zram_get_obj_size(zram, index);

	if (size != PAGE_SIZE) {
		prio = zram_get_priority(zram, index);
		zstrm = zcomp_stream_get(zram->comps[prio]);
	}

	src = zs_map_object(zram->mem_pool, handle, ZS_MM_RO);
	if (size == PAGE_SIZE) {
		dst = kmap_atomic(page);
		memcpy(dst, src, PAGE_SIZE);
		kunmap_atomic(dst);
		ret = 0;
	} else {
		dst = kmap_atomic(page);
		ret = zcomp_decompress(zstrm, src, size, dst);
		kunmap_atomic(dst);
		zcomp_stream_put(zram->comps[prio]);
	}
	zs_unmap_object(zram->mem_pool, handle);
	return ret;
}

static int __zram_bvec_read(struct zram *zram, struct page *page, u32 index,
			    struct bio *bio, bool partial_io)
{
	int ret;

	zram_slot_lock(zram, index);
	if (!zram_test_flag(zram, index, ZRAM_WB)) {
		/* Slot should be locked through out the function call */
		ret = zram_read_from_zspool(zram, page, index);
		zram_slot_unlock(zram, index);
	} else {
		unsigned long blk_idx = zram_get_element(zram, index);

		/* Slot should be unlocked before the function call */
		zram_slot_unlock(zram, index);

		ret = zram_bvec_read_from_bdev(zram, page, index, blk_idx, bio,
					       partial_io);
	}

	/* Should NEVER happen. Return bio error if it does. */
	if (WARN_ON(ret < 0))
		pr_err("Decompression failed! err=%d, page=%u\n", ret, index);

	return ret;
}

static int zram_bvec_read(struct zram *zram, struct bio_vec *bvec,
			  u32 index, int offset, struct bio *bio)
{
	int ret;
	struct page *page;

	page = bvec->bv_page;
	if (is_partial_io(bvec)) {
		/* Use a temporary buffer to decompress the page */
		page = alloc_page(GFP_NOIO|__GFP_HIGHMEM);
		if (!page)
			return -ENOMEM;
	}

	ret = __zram_bvec_read(zram, page, index, bio, is_partial_io(bvec));
	if (unlikely(ret))
		goto out;

	if (is_partial_io(bvec)) {
		void *dst = kmap_atomic(bvec->bv_page);
		void *src = kmap_atomic(page);

		memcpy(dst + bvec->bv_offset, src + offset, bvec->bv_len);
		kunmap_atomic(src);
		kunmap_atomic(dst);
	}
out:
	if (is_partial_io(bvec))
		__free_page(page);

	return ret;
}

/*
 * Compress @page and store it in slot @index.
 *
 * If @wb_blk is non-zero the store is conditional (used by prefetch): the
 * caller has set ZRAM_PP_SLOT on a ZRAM_WB slot, and the slot is only
 * replaced if it still holds backing device block @wb_blk and still has
 * ZRAM_PP_SLOT set (any free or access in the meantime clears ZRAM_PP_SLOT).
 * Otherwise -ESTALE is returned. On both outcomes ZRAM_PP_SLOT is cleared;
 * on other errors it is not.
 */
static int zram_write_page(struct zram *zram, struct page *page, u32 index,
			   unsigned long wb_blk)
{
	int ret = 0;
	unsigned long alloced_pages;
	unsigned long handle = 0;
	unsigned int comp_len = 0;
	void *src, *dst, *mem;
	struct zcomp_strm *zstrm;
	unsigned long element = 0;
	enum zram_pageflags flags = 0;

	mem = kmap_atomic(page);
	if (page_same_filled(mem, &element)) {
		kunmap_atomic(mem);
		/* Free memory associated with this sector now. */
		flags = ZRAM_SAME;
		atomic64_inc(&zram->stats.same_pages);
		goto out;
	}
	kunmap_atomic(mem);

compress_again:
	zstrm = zcomp_stream_get(zram->comps[ZRAM_PRIMARY_COMP]);
	src = kmap_atomic(page);
	ret = zcomp_compress(zstrm, src, &comp_len);
	kunmap_atomic(src);

	if (unlikely(ret)) {
		zcomp_stream_put(zram->comps[ZRAM_PRIMARY_COMP]);
		pr_err("Compression failed! err=%d\n", ret);
		zs_free(zram->mem_pool, handle);
		return ret;
	}

	if (comp_len >= huge_class_size)
		comp_len = PAGE_SIZE;
	/*
	 * handle allocation has 2 paths:
	 * a) fast path is executed with preemption disabled (for
	 *  per-cpu streams) and has __GFP_DIRECT_RECLAIM bit clear,
	 *  since we can't sleep;
	 * b) slow path enables preemption and attempts to allocate
	 *  the page with __GFP_DIRECT_RECLAIM bit set. we have to
	 *  put per-cpu compression stream and, thus, to re-do
	 *  the compression once handle is allocated.
	 *
	 * if we have a 'non-null' handle here then we are coming
	 * from the slow path and handle has already been allocated.
	 */
	if (!handle)
		handle = zs_malloc(zram->mem_pool, comp_len,
				__GFP_KSWAPD_RECLAIM |
				__GFP_NOWARN |
				__GFP_HIGHMEM |
				__GFP_MOVABLE |
				__GFP_CMA);
	if (!handle) {
		zcomp_stream_put(zram->comps[ZRAM_PRIMARY_COMP]);
		atomic64_inc(&zram->stats.writestall);
		handle = zs_malloc(zram->mem_pool, comp_len,
				GFP_NOIO | __GFP_HIGHMEM |
				__GFP_MOVABLE | __GFP_CMA);
		if (!handle)
			return -ENOMEM;

		if (comp_len != PAGE_SIZE)
			goto compress_again;
		/*
		 * If the page is not compressible, you need to acquire the lock and
		 * execute the code below. The zcomp_stream_get() call is needed to
		 * disable the cpu hotplug and grab the zstrm buffer back.
		 * It is necessary that the dereferencing of the zstrm variable below
		 * occurs correctly.
		 */
		zstrm = zcomp_stream_get(zram->comps[ZRAM_PRIMARY_COMP]);
	}

	alloced_pages = zs_get_total_pages(zram->mem_pool);
	update_used_max(zram, alloced_pages);

	if (zram->limit_pages && alloced_pages > zram->limit_pages) {
		zcomp_stream_put(zram->comps[ZRAM_PRIMARY_COMP]);
		zs_free(zram->mem_pool, handle);
		return -ENOMEM;
	}

	dst = zs_map_object(zram->mem_pool, handle, ZS_MM_WO);

	src = zstrm->buffer;
	if (comp_len == PAGE_SIZE)
		src = kmap_atomic(page);
	memcpy(dst, src, comp_len);
	if (comp_len == PAGE_SIZE)
		kunmap_atomic(src);

	zcomp_stream_put(zram->comps[ZRAM_PRIMARY_COMP]);
	zs_unmap_object(zram->mem_pool, handle);
	atomic64_add(comp_len, &zram->stats.compr_data_size);
out:
	/*
	 * Free memory associated with this sector
	 * before overwriting unused sectors.
	 */
	zram_slot_lock(zram, index);
	if (wb_blk) {
		bool stale = !zram_test_flag(zram, index, ZRAM_WB) ||
			     !zram_test_flag(zram, index, ZRAM_PP_SLOT) ||
			     zram_get_element(zram, index) != wb_blk;

		zram_clear_flag(zram, index, ZRAM_PP_SLOT);
		if (stale) {
			zram_slot_unlock(zram, index);
			if (flags) {
				atomic64_dec(&zram->stats.same_pages);
			} else {
				zs_free(zram->mem_pool, handle);
				atomic64_sub(comp_len,
					     &zram->stats.compr_data_size);
			}
			return -ESTALE;
		}
	}
	zram_free_page(zram, index);

	if (comp_len == PAGE_SIZE) {
		zram_set_flag(zram, index, ZRAM_HUGE);
		atomic64_inc(&zram->stats.huge_pages);
	}

	if (flags) {
		zram_set_flag(zram, index, flags);
		zram_set_element(zram, index, element);
	}  else {
		zram_set_handle(zram, index, handle);
		zram_set_obj_size(zram, index, comp_len);
	}
	zram_slot_unlock(zram, index);

	/* Update stats */
	atomic64_inc(&zram->stats.pages_stored);
	return ret;
}

static int __zram_bvec_write(struct zram *zram, struct bio_vec *bvec,
				u32 index, struct bio *bio)
{
	return zram_write_page(zram, bvec->bv_page, index, 0);
}

static int zram_bvec_write(struct zram *zram, struct bio_vec *bvec,
				u32 index, int offset, struct bio *bio)
{
	int ret;
	struct page *page = NULL;
	void *src;
	struct bio_vec vec;

	vec = *bvec;
	if (is_partial_io(bvec)) {
		void *dst;
		/*
		 * This is a partial IO. We need to read the full page
		 * before to write the changes.
		 */
		page = alloc_page(GFP_NOIO|__GFP_HIGHMEM);
		if (!page)
			return -ENOMEM;

		ret = __zram_bvec_read(zram, page, index, bio, true);
		if (ret)
			goto out;

		src = kmap_atomic(bvec->bv_page);
		dst = kmap_atomic(page);
		memcpy(dst + offset, src + bvec->bv_offset, bvec->bv_len);
		kunmap_atomic(dst);
		kunmap_atomic(src);

		vec.bv_page = page;
		vec.bv_len = PAGE_SIZE;
		vec.bv_offset = 0;
	}

	ret = __zram_bvec_write(zram, &vec, index, bio);
out:
	if (is_partial_io(bvec))
		__free_page(page);
	return ret;
}

#ifdef CONFIG_ZRAM_MULTI_COMP
#define RECOMPRESS_IDLE		(1 << 0)
#define RECOMPRESS_HUGE		(1 << 1)

static int scan_slots_for_recompress(struct zram *zram, u32 mode, u32 prio_max,
				     struct zram_pp_ctl *ctl)
{
	unsigned long nr_pages = zram->disksize >> PAGE_SHIFT;
	struct zram_pp_slot *pps = NULL;
	unsigned long index;

	for (index = 0; index < nr_pages; index++) {
		if (!pps) {
			pps = kmalloc(sizeof(*pps), GFP_NOIO | __GFP_NOWARN);
			if (!pps)
				break;
			INIT_LIST_HEAD(&pps->entry);
		}

		zram_slot_lock(zram, index);
		if (!zram_allocated(zram, index))
			goto next;

		if (mode & RECOMPRESS_IDLE &&
		    !zram_test_flag(zram, index, ZRAM_IDLE))
			goto next;

		if (mode & RECOMPRESS_HUGE &&
		    !zram_test_flag(zram, index, ZRAM_HUGE))
			goto next;

		if (zram_test_flag(zram, index, ZRAM_WB) ||
		    zram_test_flag(zram, index, ZRAM_SAME) ||
		    zram_test_flag(zram, index, ZRAM_PP_SLOT) ||
		    zram_test_flag(zram, index, ZRAM_INCOMPRESSIBLE))
			goto next;

		if (zram_get_priority(zram, index) + 1 >= prio_max)
			goto next;

		pps->index = index;
		place_pp_slot(zram, ctl, pps);
		pps = NULL;
next:
		zram_slot_unlock(zram, index);
	}

	kfree(pps);
	return 0;
}

/*
 * This function will decompress (unless it's ZRAM_HUGE) the page and then
 * attempt to compress it using provided compression algorithm priority
 * (which is potentially more effective).
 *
 * Corresponding ZRAM slot should be locked.
 */
static int recompress_slot(struct zram *zram, u32 index, struct page *page,
			   u32 threshold, u32 prio, u32 prio_max)
{
	struct zcomp_strm *zstrm = NULL;
	unsigned long handle_old;
	unsigned long handle_new;
	unsigned int comp_len_old;
	unsigned int comp_len_new;
	unsigned int class_index_old;
	unsigned int class_index_new;
	void *src, *dst;
	int ret = 0;

	handle_old = zram_get_handle(zram, index);
	if (!handle_old)
		return -EINVAL;

	comp_len_old = zram_get_obj_size(zram, index);
	/*
	 * Do not recompress objects that are already "small enough".
	 */
	if (comp_len_old < threshold)
		return 0;

	ret = zram_read_from_zspool(zram, page, index);
	if (ret)
		return ret;

	/*
	 * We touched this entry so mark it as non-IDLE. This makes sure that
	 * we don't preserve IDLE flag and don't incorrectly pick this entry
	 * for different post-processing type (e.g. writeback).
	 */
	zram_clear_flag(zram, index, ZRAM_IDLE);

	class_index_old = zs_lookup_class_index(zram->mem_pool, comp_len_old);
	/*
	 * Iterate the secondary comp algorithms list (in order of priority)
	 * and try to recompress the page.
	 */
	for (; prio < prio_max; prio++) {
		if (!zram->comps[prio])
			continue;

		/*
		 * Skip if the object is already re-compressed with a higher
		 * priority algorithm (or same algorithm).
		 */
		if (prio <= zram_get_priority(zram, index))
			continue;

		zstrm = zcomp_stream_get(zram->comps[prio]);
		src = kmap_atomic(page);
		ret = zcomp_compress(zstrm, src, &comp_len_new);
		kunmap_atomic(src);

		if (ret) {
			zcomp_stream_put(zram->comps[prio]);
			zstrm = NULL;
			break;
		}

		class_index_new = zs_lookup_class_index(zram->mem_pool,
							comp_len_new);

		/* Continue until we make progress */
		if (class_index_new >= class_index_old ||
		    (threshold && comp_len_new >= threshold)) {
			zcomp_stream_put(zram->comps[prio]);
			zstrm = NULL;
			continue;
		}

		/* Recompression was successful so break out */
		break;
	}

	/* Compression error */
	if (ret)
		return ret;

	if (!zstrm) {
		/*
		 * Secondary algorithms failed to re-compress the page
		 * in a way that would save memory.
		 *
		 * Mark the object incompressible if the max-priority
		 * algorithm couldn't re-compress it.
		 */
		if (prio < zram->num_active_comps)
			return 0;
		zram_set_flag(zram, index, ZRAM_INCOMPRESSIBLE);
		return 0;
	}

	/*
	 * No direct reclaim (slow path) for handle allocation and no
	 * re-compression attempt (unlike in __zram_bvec_write()) since
	 * we already have stored that object in zsmalloc. If we cannot
	 * alloc memory for recompressed object then we bail out and
	 * simply keep the old (existing) object in zsmalloc.
	 */
	handle_new = zs_malloc(zram->mem_pool, comp_len_new,
			       __GFP_KSWAPD_RECLAIM |
			       __GFP_NOWARN |
			       __GFP_HIGHMEM |
			       __GFP_MOVABLE |
			       __GFP_CMA);
	if (!handle_new) {
		zcomp_stream_put(zram->comps[prio]);
		return -ENOMEM;
	}

	dst = zs_map_object(zram->mem_pool, handle_new, ZS_MM_WO);
	memcpy(dst, zstrm->buffer, comp_len_new);
	zcomp_stream_put(zram->comps[prio]);

	zs_unmap_object(zram->mem_pool, handle_new);

	zram_free_page(zram, index);
	zram_set_handle(zram, index, handle_new);
	zram_set_obj_size(zram, index, comp_len_new);
	zram_set_priority(zram, index, prio);

	atomic64_add(comp_len_new, &zram->stats.compr_data_size);
	atomic64_inc(&zram->stats.pages_stored);

	return 0;
}

static ssize_t recompress_store(struct device *dev,
				struct device_attribute *attr,
				const char *buf, size_t len)
{
	u32 prio = ZRAM_SECONDARY_COMP, prio_max = ZRAM_MAX_COMPS;
	struct zram *zram = dev_to_zram(dev);
	char *args, *param, *val, *algo = NULL;
	struct zram_pp_ctl *ctl = NULL;
	struct zram_pp_slot *pps;
	u32 mode = 0, threshold = 0;
	struct page *page = NULL;
	ssize_t ret;

	args = skip_spaces(buf);
	while (*args) {
		args = next_arg(args, &param, &val);

		if (!val || !*val)
			return -EINVAL;

		if (!strcmp(param, "type")) {
			if (!strcmp(val, "idle"))
				mode = RECOMPRESS_IDLE;
			if (!strcmp(val, "huge"))
				mode = RECOMPRESS_HUGE;
			if (!strcmp(val, "huge_idle"))
				mode = RECOMPRESS_IDLE | RECOMPRESS_HUGE;
			continue;
		}

		if (!strcmp(param, "threshold")) {
			/*
			 * We will re-compress only idle objects equal or
			 * greater in size than watermark.
			 */
			ret = kstrtouint(val, 10, &threshold);
			if (ret)
				return ret;
			continue;
		}

		if (!strcmp(param, "algo")) {
			algo = val;
			continue;
		}
	}

	if (threshold >= PAGE_SIZE)
		return -EINVAL;

	down_read(&zram->init_lock);
	if (!init_done(zram)) {
		ret = -EINVAL;
		goto release_init_lock;
	}

	if (algo) {
		bool found = false;

		for (; prio < ZRAM_MAX_COMPS; prio++) {
			if (!zram->comp_algs[prio])
				continue;

			if (!strcmp(zram->comp_algs[prio], algo)) {
				prio_max = min(prio + 1, ZRAM_MAX_COMPS);
				found = true;
				break;
			}
		}

		if (!found) {
			ret = -EINVAL;
			goto release_init_lock;
		}
	}

	page = alloc_page(GFP_KERNEL);
	if (!page) {
		ret = -ENOMEM;
		goto release_init_lock;
	}

	ctl = init_pp_ctl();
	if (!ctl) {
		ret = -ENOMEM;
		goto release_init_lock;
	}

	scan_slots_for_recompress(zram, mode, prio_max, ctl);

	ret = len;
	while ((pps = select_pp_slot(ctl))) {
		int err = 0;

		zram_slot_lock(zram, pps->index);
		if (!zram_test_flag(zram, pps->index, ZRAM_PP_SLOT))
			goto next;

		err = recompress_slot(zram, pps->index, page, threshold,
				      prio, prio_max);
next:
		zram_slot_unlock(zram, pps->index);
		release_pp_slot(zram, pps);

		if (err) {
			ret = err;
			break;
		}

		cond_resched();
	}

release_init_lock:
	if (page)
		__free_page(page);
	release_pp_ctl(zram, ctl);
	up_read(&zram->init_lock);
	return ret;
}
#endif

/*
 * zram_bio_discard - handler on discard request
 * @index: physical block index in PAGE_SIZE units
 * @offset: byte offset within physical block
 */
static void zram_bio_discard(struct zram *zram, u32 index,
			     int offset, struct bio *bio)
{
	size_t n = bio->bi_iter.bi_size;

	/*
	 * zram manages data in physical block size units. Because logical block
	 * size isn't identical with physical block size on some arch, we
	 * could get a discard request pointing to a specific offset within a
	 * certain physical block.  Although we can handle this request by
	 * reading that physiclal block and decompressing and partially zeroing
	 * and re-compressing and then re-storing it, this isn't reasonable
	 * because our intent with a discard request is to save memory.  So
	 * skipping this logical block is appropriate here.
	 */
	if (offset) {
		if (n <= (PAGE_SIZE - offset))
			return;

		n -= (PAGE_SIZE - offset);
		index++;
	}

	while (n >= PAGE_SIZE) {
		zram_slot_lock(zram, index);
		zram_free_page(zram, index);
		zram_slot_unlock(zram, index);
		atomic64_inc(&zram->stats.notify_free);
		index++;
		n -= PAGE_SIZE;
	}
}

/*
 * Returns errno if it has some problem. Otherwise return 0 or 1.
 * Returns 0 if IO request was done synchronously
 * Returns 1 if IO request was successfully submitted.
 */
static int zram_bvec_rw(struct zram *zram, struct bio_vec *bvec, u32 index,
			int offset, unsigned int op, struct bio *bio)
{
	int ret;

	if (!op_is_write(op)) {
		ret = zram_bvec_read(zram, bvec, index, offset, bio);
		flush_dcache_page(bvec->bv_page);
	} else {
		ret = zram_bvec_write(zram, bvec, index, offset, bio);
	}

	zram_slot_lock(zram, index);
	zram_accessed(zram, index);
	zram_slot_unlock(zram, index);

	if (unlikely(ret < 0)) {
		if (!op_is_write(op))
			atomic64_inc(&zram->stats.failed_reads);
		else
			atomic64_inc(&zram->stats.failed_writes);
	}

	return ret;
}

static void __zram_make_request(struct zram *zram, struct bio *bio)
{
	int offset;
	u32 index;
	struct bio_vec bvec;
	struct bvec_iter iter;
	unsigned long start_time;

	index = bio->bi_iter.bi_sector >> SECTORS_PER_PAGE_SHIFT;
	offset = (bio->bi_iter.bi_sector &
		  (SECTORS_PER_PAGE - 1)) << SECTOR_SHIFT;

	switch (bio_op(bio)) {
	case REQ_OP_DISCARD:
	case REQ_OP_WRITE_ZEROES:
		zram_bio_discard(zram, index, offset, bio);
		bio_endio(bio);
		return;
	default:
		break;
	}

	start_time = bio_start_io_acct(bio);
	bio_for_each_segment(bvec, bio, iter) {
		struct bio_vec bv = bvec;
		unsigned int unwritten = bvec.bv_len;

		do {
			bv.bv_len = min_t(unsigned int, PAGE_SIZE - offset,
							unwritten);
			if (zram_bvec_rw(zram, &bv, index, offset,
					 bio_op(bio), bio) < 0) {
				bio->bi_status = BLK_STS_IOERR;
				break;
			}

			bv.bv_offset += bv.bv_len;
			unwritten -= bv.bv_len;

			update_position(&index, &offset, &bv);
		} while (unwritten);
	}
	bio_end_io_acct(bio, start_time);
	bio_endio(bio);
}

/*
 * Handler function for all zram I/O requests.
 */
static blk_qc_t zram_submit_bio(struct bio *bio)
{
	struct zram *zram = bio->bi_disk->private_data;

	if (!valid_io_request(zram, bio->bi_iter.bi_sector,
					bio->bi_iter.bi_size)) {
		atomic64_inc(&zram->stats.invalid_io);
		goto error;
	}

	__zram_make_request(zram, bio);
	return BLK_QC_T_NONE;

error:
	bio_io_error(bio);
	return BLK_QC_T_NONE;
}

static void zram_slot_free_notify(struct block_device *bdev,
				unsigned long index)
{
	struct zram *zram;

	zram = bdev->bd_disk->private_data;

	atomic64_inc(&zram->stats.notify_free);
	if (!zram_slot_trylock(zram, index)) {
		atomic64_inc(&zram->stats.miss_free);
		return;
	}

	zram_free_page(zram, index);
	zram_slot_unlock(zram, index);
}

static int zram_rw_page(struct block_device *bdev, sector_t sector,
		       struct page *page, unsigned int op)
{
	int offset, ret;
	u32 index;
	struct zram *zram;
	struct bio_vec bv;
	unsigned long start_time;

	if (PageTransHuge(page))
		return -ENOTSUPP;
	zram = bdev->bd_disk->private_data;

	if (!valid_io_request(zram, sector, PAGE_SIZE)) {
		atomic64_inc(&zram->stats.invalid_io);
		ret = -EINVAL;
		goto out;
	}

	index = sector >> SECTORS_PER_PAGE_SHIFT;
	offset = (sector & (SECTORS_PER_PAGE - 1)) << SECTOR_SHIFT;

	bv.bv_page = page;
	bv.bv_len = PAGE_SIZE;
	bv.bv_offset = 0;

	start_time = disk_start_io_acct(bdev->bd_disk, SECTORS_PER_PAGE, op);
	ret = zram_bvec_rw(zram, &bv, index, offset, op, NULL);
	disk_end_io_acct(bdev->bd_disk, op, start_time);
out:
	/*
	 * If I/O fails, just return error(ie, non-zero) without
	 * calling page_endio.
	 * It causes resubmit the I/O with bio request by upper functions
	 * of rw_page(e.g., swap_readpage, __swap_writepage) and
	 * bio->bi_end_io does things to handle the error
	 * (e.g., SetPageError, set_page_dirty and extra works).
	 */
	if (unlikely(ret < 0))
		return ret;

	switch (ret) {
	case 0:
		page_endio(page, op_is_write(op), 0);
		break;
	case 1:
		ret = 0;
		break;
	default:
		WARN_ON(1);
	}
	return ret;
}

static void zram_destroy_comps(struct zram *zram)
{
	u32 prio;

	for (prio = 0; prio < ZRAM_MAX_COMPS; prio++) {
		struct zcomp *comp = zram->comps[prio];

		zram->comps[prio] = NULL;
		if (!comp)
			continue;
		zcomp_destroy(comp);
		zram->num_active_comps--;
	}
}

static void zram_reset_device(struct zram *zram)
{
	down_write(&zram->init_lock);

	zram->limit_pages = 0;

	if (!init_done(zram)) {
		up_write(&zram->init_lock);
		return;
	}

	set_capacity(zram->disk, 0);
	part_stat_set_all(&zram->disk->part0, 0);

	/* I/O operation under all of CPU are done so let's free */
	zram_meta_free(zram, zram->disksize);
	zram->disksize = 0;
	zram_destroy_comps(zram);
	memset(&zram->stats, 0, sizeof(zram->stats));
	reset_bdev(zram);

	comp_algorithm_set(zram, ZRAM_PRIMARY_COMP, default_compressor);
	up_write(&zram->init_lock);
}

static ssize_t disksize_store(struct device *dev,
		struct device_attribute *attr, const char *buf, size_t len)
{
	u64 disksize;
	struct zcomp *comp;
	struct zram *zram = dev_to_zram(dev);
	int err;
	u32 prio;

	disksize = memparse(buf, NULL);
	if (!disksize)
		return -EINVAL;

	down_write(&zram->init_lock);
	if (init_done(zram)) {
		pr_info("Cannot change disksize for initialized device\n");
		err = -EBUSY;
		goto out_unlock;
	}

	disksize = PAGE_ALIGN(disksize);
	if (!zram_meta_alloc(zram, disksize)) {
		err = -ENOMEM;
		goto out_unlock;
	}

	for (prio = 0; prio < ZRAM_MAX_COMPS; prio++) {
		if (!zram->comp_algs[prio])
			continue;

		comp = zcomp_create(zram->comp_algs[prio]);
		if (IS_ERR(comp)) {
			pr_err("Cannot initialise %s compressing backend\n",
			       zram->comp_algs[prio]);
			err = PTR_ERR(comp);
			goto out_free_comps;
		}

		zram->comps[prio] = comp;
		zram->num_active_comps++;
	}
	zram->disksize = disksize;
	set_capacity(zram->disk, zram->disksize >> SECTOR_SHIFT);

	revalidate_disk_size(zram->disk, true);
	up_write(&zram->init_lock);

	return len;

out_free_comps:
	zram_destroy_comps(zram);
	zram_meta_free(zram, disksize);
out_unlock:
	up_write(&zram->init_lock);
	return err;
}

static ssize_t reset_store(struct device *dev,
		struct device_attribute *attr, const char *buf, size_t len)
{
	int ret;
	unsigned short do_reset;
	struct zram *zram;
	struct block_device *bdev;

	ret = kstrtou16(buf, 10, &do_reset);
	if (ret)
		return ret;

	if (!do_reset)
		return -EINVAL;

	zram = dev_to_zram(dev);
	bdev = bdget_disk(zram->disk, 0);
	if (!bdev)
		return -ENOMEM;

	mutex_lock(&bdev->bd_mutex);
	/* Do not reset an active device or claimed device */
	if (bdev->bd_openers || zram->claim) {
		mutex_unlock(&bdev->bd_mutex);
		bdput(bdev);
		return -EBUSY;
	}

	/* From now on, anyone can't open /dev/zram[0-9] */
	zram->claim = true;
	mutex_unlock(&bdev->bd_mutex);

	/* Make sure all the pending I/O are finished */
	fsync_bdev(bdev);
	zram_reset_device(zram);
	revalidate_disk_size(zram->disk, true);
	bdput(bdev);

	mutex_lock(&bdev->bd_mutex);
	zram->claim = false;
	mutex_unlock(&bdev->bd_mutex);

	return len;
}

static int zram_open(struct block_device *bdev, fmode_t mode)
{
	int ret = 0;
	struct zram *zram;

	WARN_ON(!mutex_is_locked(&bdev->bd_mutex));

	zram = bdev->bd_disk->private_data;
	/* zram was claimed to reset so open request fails */
	if (zram->claim)
		ret = -EBUSY;

	return ret;
}

#ifdef CONFIG_ZRAM_ANDROID_IOCTL
/*
 * Android per-process zram ioctls (ZRAM_ANDROID_IOC_*, version 1), adapted
 * from ACK android16-6.12 drivers/block/zram/zram_ioctl.c for 5.10:
 * - 5.10 has no zram_pp_ctl/zram_wb_ctl; candidate slots are collected in a
 *   bitmap and processed with the sysfs writeback per-slot helper.
 * - 5.10 writes back decompressed pages, so prefetch reads the page and
 *   recompresses it (conditional store, see zram_write_page()).
 * - The legacy ZRAM_ANDROID_IOC_PROCESS_WRITEBACK (neverallowed by sepolicy)
 *   is not implemented.
 */
#define ZRAM_NR_PAGES_UNLIMITED	U64_MAX

struct zram_process_walk_private {
	struct zram *zram;
	unsigned long *slots;		/* bitmap of candidate zram slots */
	u64 nr_remaining_pages;
	unsigned long next_addr;
};

static inline bool zram_can_do_file_pageout(struct vm_area_struct *vma)
{
	if (!vma->vm_file)
		return false;
	/*
	 * paging out pagecache only for non-anonymous mappings that correspond
	 * to the files the calling process could (if tried) open for writing;
	 * otherwise we would be including shared non-exclusive mappings, which
	 * opens a side channel.
	 */
	return inode_owner_or_capable(file_inode(vma->vm_file)) ||
		inode_permission(file_inode(vma->vm_file), MAY_WRITE) == 0;
}

static int zram_process_walker(pmd_t *pmd, unsigned long start,
			       unsigned long end, struct mm_walk *walk)
{
	struct zram_process_walk_private *priv = walk->private;
	struct zram *zram = priv->zram;
	unsigned long nr_pages = zram->disksize >> PAGE_SHIFT;
	pte_t *start_pte, *ptep;
	spinlock_t *ptl;
	unsigned long addr;
	int ret = 0;

	if (pmd_trans_unstable(pmd))
		return 0;

	start_pte = ptep = pte_offset_map_lock(walk->mm, pmd, start, &ptl);
	for (addr = start; addr < end; addr += PAGE_SIZE, ptep++) {
		struct swap_info_struct *sis;
		swp_entry_t entry;
		pte_t pte = *ptep;
		pgoff_t index;

		if (priv->nr_remaining_pages == 0) {
			priv->next_addr = addr;
			ret = 1;
			break;
		}

		if (!is_swap_pte(pte))
			continue;
		entry = pte_to_swp_entry(pte);
		if (unlikely(non_swap_entry(entry)))
			continue;

		/*
		 * The PTE lock is held and the PTE still holds this swap
		 * entry, so swapoff cannot have finished with this device.
		 */
		sis = swp_swap_info(entry);
		if (unlikely(!sis || !sis->bdev || !sis->bdev->bd_disk ||
			     sis->bdev->bd_disk->private_data != zram))
			continue;

		index = swp_offset(entry);
		if (unlikely(index >= nr_pages))
			continue;

		__set_bit(index, priv->slots);
		if (priv->nr_remaining_pages != ZRAM_NR_PAGES_UNLIMITED)
			priv->nr_remaining_pages--;
	}
	pte_unmap_unlock(start_pte, ptl);
	cond_resched();

	return ret;
}

static const struct mm_walk_ops zram_process_walk_ops = {
	.pmd_entry = zram_process_walker,
};

/*
 * Collect the zram slots holding swapped-out pages of the process behind
 * @pidfd, starting at @start_addr and stopping after @size bytes worth of
 * candidates (0 = unlimited). *next_addr is where a size-limited scan
 * stopped, or 0 if it reached the end of the address space.
 */
static int zram_process_scan(struct zram *zram, u64 pidfd, u64 start_addr,
			     u64 size, unsigned long *slots, u64 *next_addr)
{
	struct zram_process_walk_private priv = {
		.zram = zram,
		.slots = slots,
	};
	struct vm_area_struct *vma;
	struct task_struct *task;
	struct mm_struct *mm;
	unsigned int f_flags;
	struct pid *pid;
	int ret = 0;

	*next_addr = 0;
	priv.nr_remaining_pages = size ? DIV_ROUND_UP(size, PAGE_SIZE) :
					  ZRAM_NR_PAGES_UNLIMITED;

	if (pidfd > INT_MAX)
		return -EBADF;
	if (!IS_ALIGNED(start_addr, PAGE_SIZE))
		return -EINVAL;

	pid = pidfd_get_pid(pidfd, &f_flags);
	if (IS_ERR(pid))
		return PTR_ERR(pid);
	task = get_pid_task(pid, PIDTYPE_TGID);
	put_pid(pid);
	if (!task)
		return -ESRCH;

	mm = get_task_mm(task);
	if (!mm) {
		ret = -ESRCH;
		goto release_task;
	}

	if (start_addr >= mm->task_size) {
		ret = -EINVAL;
		goto release_mm;
	}

	mmap_read_lock(mm);
	for (vma = find_vma(mm, start_addr); vma; vma = vma->vm_next) {
		unsigned long start = max_t(unsigned long, vma->vm_start,
					    start_addr);

		if (!vma_is_anonymous(vma) && !zram_can_do_file_pageout(vma) &&
		    (vma->vm_flags & VM_MAYSHARE))
			continue;

		ret = walk_page_range(mm, start, vma->vm_end,
				      &zram_process_walk_ops, &priv);
		if (ret)
			break;
	}
	mmap_read_unlock(mm);

	if (ret > 0) {
		*next_addr = priv.next_addr;
		ret = 0;
	}
release_mm:
	mmput(mm);
release_task:
	put_task_struct(task);
	return ret;
}

/*
 * Complete a single async prefetch read bio.
 *
 * When zram->compressed_wb is enabled, the backing-device page already holds
 * the compressed zsmalloc object: allocate a zsmalloc handle of the exact
 * preserved size, copy the compressed bytes straight in (0 decompressions,
 * 0 recompressions), restore the slot handle/stats, and free the bdev block.
 * Otherwise fall back to conditional zram_write_page() recompression.
 */
static int zram_prefetch_complete(struct zram *zram, struct zram_wb_req *req,
				  u64 *read_bytes)
{
	u32 index = req->index;
	int err;

	err = blk_status_to_errno(req->bio.bi_status);
	if (err) {
		zram_slot_lock(zram, index);
		zram_clear_flag(zram, index, ZRAM_PP_SLOT);
		zram_slot_unlock(zram, index);
		return err;
	}

	if (zram->compressed_wb) {
		unsigned long handle, alloced_pages;
		unsigned int size;
		void *src, *dst;

		zram_slot_lock(zram, index);
		if (!zram_test_flag(zram, index, ZRAM_WB) ||
		    !zram_test_flag(zram, index, ZRAM_PP_SLOT) ||
		    zram_get_element(zram, index) != req->blk_idx) {
			zram_clear_flag(zram, index, ZRAM_PP_SLOT);
			zram_slot_unlock(zram, index);
			return 0;
		}

		size = zram_get_obj_size(zram, index);
		if (unlikely(!size || size > PAGE_SIZE)) {
			zram_clear_flag(zram, index, ZRAM_PP_SLOT);
			zram_slot_unlock(zram, index);
			return -EIO;
		}

		handle = zs_malloc(zram->mem_pool, size,
				   __GFP_KSWAPD_RECLAIM | __GFP_NOWARN |
				   __GFP_HIGHMEM | __GFP_MOVABLE | __GFP_CMA);
		if (!handle) {
			zram_slot_unlock(zram, index);
			handle = zs_malloc(zram->mem_pool, size,
					   GFP_NOIO | __GFP_HIGHMEM |
					   __GFP_MOVABLE | __GFP_CMA);
			if (!handle) {
				zram_slot_lock(zram, index);
				zram_clear_flag(zram, index, ZRAM_PP_SLOT);
				zram_slot_unlock(zram, index);
				return -ENOMEM;
			}
			zram_slot_lock(zram, index);
			if (!zram_test_flag(zram, index, ZRAM_WB) ||
			    !zram_test_flag(zram, index, ZRAM_PP_SLOT) ||
			    zram_get_element(zram, index) != req->blk_idx ||
			    zram_get_obj_size(zram, index) != size) {
				zram_clear_flag(zram, index, ZRAM_PP_SLOT);
				zram_slot_unlock(zram, index);
				zs_free(zram->mem_pool, handle);
				return 0;
			}
		}

		alloced_pages = zs_get_total_pages(zram->mem_pool);
		update_used_max(zram, alloced_pages);
		if (zram->limit_pages && alloced_pages > zram->limit_pages) {
			zram_clear_flag(zram, index, ZRAM_PP_SLOT);
			zram_slot_unlock(zram, index);
			zs_free(zram->mem_pool, handle);
			return -ENOMEM;
		}

		dst = zs_map_object(zram->mem_pool, handle, ZS_MM_WO);
		src = kmap_atomic(req->page);
		memcpy(dst, src, size);
		kunmap_atomic(src);
		zs_unmap_object(zram->mem_pool, handle);

		zram_clear_flag(zram, index, ZRAM_WB);
		free_block_bdev(zram, req->blk_idx);
		if (zram_test_flag(zram, index, ZRAM_HUGE))
			atomic64_inc(&zram->stats.huge_pages);
		zram_set_handle(zram, index, handle);
		zram_accessed(zram, index);
		atomic64_add(size, &zram->stats.compr_data_size);
		zram_slot_unlock(zram, index);

		if (read_bytes)
			*read_bytes += PAGE_SIZE;
		return 0;
	}

	err = zram_write_page(zram, req->page, index, req->blk_idx);
	if (err == -ESTALE)
		return 0;
	if (err) {
		zram_slot_lock(zram, index);
		zram_clear_flag(zram, index, ZRAM_PP_SLOT);
		zram_slot_unlock(zram, index);
		return err;
	}

	zram_slot_lock(zram, index);
	zram_accessed(zram, index);
	zram_slot_unlock(zram, index);
	if (read_bytes)
		*read_bytes += PAGE_SIZE;
	return 0;
}

static int zram_complete_prefetch_reqs(struct zram *zram,
				       struct zram_wb_ctl *wb_ctl,
				       u64 *read_bytes)
{
	struct zram_wb_req *req;
	unsigned long flags;
	int ret = 0, err;

	while (atomic_read(&wb_ctl->num_inflight) > 0) {
		spin_lock_irqsave(&wb_ctl->done_lock, flags);
		req = list_first_entry_or_null(&wb_ctl->done_reqs,
					       struct zram_wb_req, entry);
		if (req)
			list_del(&req->entry);
		spin_unlock_irqrestore(&wb_ctl->done_lock, flags);

		if (!req)
			break;

		err = zram_prefetch_complete(zram, req, read_bytes);
		if (err)
			ret = err;

		atomic_dec(&wb_ctl->num_inflight);
		list_add(&req->entry, &wb_ctl->idle_reqs);
	}

	return ret;
}

static int zram_ioctl_process_prefetch(struct zram *zram,
				       unsigned long *slots,
				       unsigned long nr_pages,
				       u64 *read_bytes)
{
	struct zram_wb_ctl *wb_ctl;
	struct zram_wb_req *req = NULL;
	unsigned long index;
	int ret = 0, err;

	wb_ctl = init_wb_ctl(zram);
	if (!wb_ctl)
		return -ENOMEM;

	for_each_set_bit(index, slots, nr_pages) {
		unsigned long blk_idx;

		if (fatal_signal_pending(current)) {
			ret = -EINTR;
			break;
		}

		while (!req) {
			req = zram_select_idle_req(wb_ctl);
			if (req)
				break;

			wait_event(wb_ctl->done_wait,
				   !list_empty(&wb_ctl->done_reqs));
			err = zram_complete_prefetch_reqs(zram, wb_ctl,
							  read_bytes);
			if (err) {
				ret = err;
				if (err == -ENOMEM)
					break;
			}
		}
		if (!req)
			break;

		zram_slot_lock(zram, index);
		if (!zram_test_flag(zram, index, ZRAM_WB) ||
		    zram_test_flag(zram, index, ZRAM_PP_SLOT)) {
			zram_slot_unlock(zram, index);
			continue;
		}
		blk_idx = zram_get_element(zram, index);
		zram_set_flag(zram, index, ZRAM_PP_SLOT);
		zram_slot_unlock(zram, index);

		req->blk_idx = blk_idx;
		req->index = index;
		req->pps = NULL;
		bio_init(&req->bio, &req->bio_vec, 1);
		bio_set_dev(&req->bio, zram->bdev);
		req->bio.bi_iter.bi_sector = blk_idx * (PAGE_SIZE >> 9);
		req->bio.bi_opf = REQ_OP_READ;
		req->bio.bi_end_io = zram_writeback_endio;
		req->bio.bi_private = wb_ctl;
		bio_add_page(&req->bio, req->page, PAGE_SIZE, 0);

		atomic64_inc(&zram->stats.bd_reads);
		atomic_inc(&wb_ctl->num_inflight);
		submit_bio(&req->bio);
		req = NULL;
		cond_resched();
	}

	if (req)
		release_wb_req(req);

	while (atomic_read(&wb_ctl->num_inflight) > 0) {
		wait_event(wb_ctl->done_wait, !list_empty(&wb_ctl->done_reqs));
		err = zram_complete_prefetch_reqs(zram, wb_ctl, read_bytes);
		if (err)
			ret = err;
	}

	release_wb_ctl(wb_ctl);
	return ret;
}

static int zram_ioctl_process_writeback(struct zram *zram,
					unsigned long *slots,
					unsigned long nr_pages,
					u64 *written_bytes)
{
	struct zram_pp_ctl *pp_ctl = NULL;
	struct zram_wb_ctl *wb_ctl = NULL;
	struct zram_pp_slot *pps = NULL;
	unsigned long index;
	int ret;

	pp_ctl = init_pp_ctl();
	if (!pp_ctl)
		return -ENOMEM;

	wb_ctl = init_wb_ctl(zram);
	if (!wb_ctl) {
		ret = -ENOMEM;
		goto out;
	}

	for_each_set_bit(index, slots, nr_pages) {
		if (!pps) {
			pps = kmalloc(sizeof(*pps), GFP_NOIO | __GFP_NOWARN);
			if (!pps)
				break;
			INIT_LIST_HEAD(&pps->entry);
		}

		zram_slot_lock(zram, index);
		if (!zram_allocated(zram, index) ||
		    zram_test_flag(zram, index, ZRAM_WB) ||
		    zram_test_flag(zram, index, ZRAM_SAME) ||
		    zram_test_flag(zram, index, ZRAM_PP_SLOT)) {
			zram_slot_unlock(zram, index);
			continue;
		}
		pps->index = index;
		place_pp_slot(zram, pp_ctl, pps);
		pps = NULL;
		zram_slot_unlock(zram, index);
	}
	kfree(pps);

	ret = zram_writeback_slots(zram, pp_ctl, wb_ctl, written_bytes);
out:
	release_pp_ctl(zram, pp_ctl);
	release_wb_ctl(wb_ctl);
	return ret;
}

static int zram_ioctl_process(struct zram *zram, bool prefetch, u64 pidfd,
			      u64 start_addr, u64 size, u64 *next_addr,
			      u64 *done_bytes)
{
	unsigned long nr_pages;
	unsigned long *slots = NULL;
	int ret;

	*next_addr = 0;
	*done_bytes = 0;

	/* Require CAP_SYS_NICE for influencing process performance. */
	if (!capable(CAP_SYS_NICE))
		return -EPERM;

	down_read(&zram->init_lock);
	if (!init_done(zram)) {
		ret = -EINVAL;
		goto out_unlock;
	}
	if (!zram->backing_dev) {
		ret = -ENODEV;
		goto out_unlock;
	}

	nr_pages = zram->disksize >> PAGE_SHIFT;
	slots = kvcalloc(BITS_TO_LONGS(nr_pages), sizeof(unsigned long),
			 GFP_KERNEL);
	if (!slots) {
		ret = -ENOMEM;
		goto out_unlock;
	}

	ret = zram_process_scan(zram, pidfd, start_addr, size, slots,
				next_addr);
	if (ret)
		goto out_free;

	if (prefetch)
		ret = zram_ioctl_process_prefetch(zram, slots, nr_pages,
						  done_bytes);
	else
		ret = zram_ioctl_process_writeback(zram, slots, nr_pages,
						   done_bytes);

out_free:
	kvfree(slots);
out_unlock:
	up_read(&zram->init_lock);
	return ret;
}

static int zram_ioctl_process_prefetch_user(struct zram *zram,
					    unsigned int cmd, void __user *argp)
{
	struct zram_android_ioc_process_prefetch kprefetch;
	size_t usize = _IOC_SIZE(cmd);
	u64 next_addr;
	int ret;

	BUILD_BUG_ON(offsetofend(struct zram_android_ioc_process_prefetch,
				 pidfd) !=
		     ZRAM_ANDROID_IOC_PROCESS_PREFETCH_SIZE_VER0);
	BUILD_BUG_ON(sizeof(kprefetch) !=
		     ZRAM_ANDROID_IOC_PROCESS_PREFETCH_SIZE_VER1);

	if (!(_IOC_DIR(cmd) & _IOC_WRITE) ||
	    usize < ZRAM_ANDROID_IOC_PROCESS_PREFETCH_SIZE_VER0)
		return -ENOTTY;

	ret = copy_struct_from_user(&kprefetch, sizeof(kprefetch), argp,
				    usize);
	if (ret)
		return ret;
	if (kprefetch.flags)
		return -EINVAL;

	kprefetch.size = sizeof(kprefetch);
	ret = zram_ioctl_process(zram, true, kprefetch.pidfd, 0, 0,
				 &next_addr, &kprefetch.read_bytes);

	if ((_IOC_DIR(cmd) & _IOC_READ) &&
	    copy_to_user(argp, &kprefetch, min(usize, sizeof(kprefetch))))
		ret = -EFAULT;
	return ret;
}

static int zram_ioctl(struct block_device *bdev, fmode_t mode,
		      unsigned int cmd, unsigned long arg)
{
	struct zram *zram = bdev->bd_disk->private_data;
	void __user *argp = (void __user *)arg;

	if (cmd == ZRAM_ANDROID_IOC_GET_VERSION)
		return ZRAM_ANDROID_IOC_VERSION;

	if (cmd == ZRAM_ANDROID_IOC_PROCESS_RANGE_WRITEBACK) {
		struct zram_android_ioc_process_range_writeback prwb;
		int ret;

		if (copy_from_user(&prwb, argp, sizeof(prwb)))
			return -EFAULT;

		ret = zram_ioctl_process(zram, false, prwb.pidfd,
					 prwb.start_addr, prwb.size,
					 &prwb.next_addr, &prwb.written_bytes);

		if (copy_to_user(argp, &prwb, sizeof(prwb)))
			ret = -EFAULT;
		return ret;
	}

	if (_IOC_TYPE(cmd) == ZRAM_ANDROID_IOC_MAGIC &&
	    _IOC_NR(cmd) == _IOC_NR(ZRAM_ANDROID_IOC_PROCESS_PREFETCH))
		return zram_ioctl_process_prefetch_user(zram, cmd, argp);

	return -ENOTTY;
}
#endif /* CONFIG_ZRAM_ANDROID_IOCTL */

static const struct block_device_operations zram_devops = {
	.open = zram_open,
	.submit_bio = zram_submit_bio,
	.swap_slot_free_notify = zram_slot_free_notify,
	.rw_page = zram_rw_page,
#ifdef CONFIG_ZRAM_ANDROID_IOCTL
	.ioctl = zram_ioctl,
#endif
	.owner = THIS_MODULE
};

static const struct block_device_operations zram_wb_devops = {
	.open = zram_open,
	.submit_bio = zram_submit_bio,
	.swap_slot_free_notify = zram_slot_free_notify,
#ifdef CONFIG_ZRAM_ANDROID_IOCTL
	.ioctl = zram_ioctl,
#endif
	.owner = THIS_MODULE
};

static DEVICE_ATTR_WO(compact);
static DEVICE_ATTR_RW(disksize);
static DEVICE_ATTR_RO(initstate);
static DEVICE_ATTR_WO(reset);
static DEVICE_ATTR_WO(mem_limit);
static DEVICE_ATTR_WO(mem_used_max);
static DEVICE_ATTR_WO(idle);
static DEVICE_ATTR_RW(max_comp_streams);
static DEVICE_ATTR_RW(comp_algorithm);
#ifdef CONFIG_ZRAM_WRITEBACK
static DEVICE_ATTR_RW(backing_dev);
static DEVICE_ATTR_WO(writeback);
static DEVICE_ATTR_RW(writeback_limit);
static DEVICE_ATTR_RW(writeback_limit_enable);
static DEVICE_ATTR_RW(writeback_batch_size);
static DEVICE_ATTR_RW(compressed_writeback);
#endif
#ifdef CONFIG_ZRAM_MULTI_COMP
static DEVICE_ATTR_RW(recomp_algorithm);
static DEVICE_ATTR_WO(recompress);
#endif

static struct attribute *zram_disk_attrs[] = {
	&dev_attr_disksize.attr,
	&dev_attr_initstate.attr,
	&dev_attr_reset.attr,
	&dev_attr_compact.attr,
	&dev_attr_mem_limit.attr,
	&dev_attr_mem_used_max.attr,
	&dev_attr_idle.attr,
	&dev_attr_max_comp_streams.attr,
	&dev_attr_comp_algorithm.attr,
#ifdef CONFIG_ZRAM_WRITEBACK
	&dev_attr_backing_dev.attr,
	&dev_attr_writeback.attr,
	&dev_attr_writeback_limit.attr,
	&dev_attr_writeback_limit_enable.attr,
	&dev_attr_writeback_batch_size.attr,
	&dev_attr_compressed_writeback.attr,
#endif
	&dev_attr_io_stat.attr,
	&dev_attr_mm_stat.attr,
#ifdef CONFIG_ZRAM_WRITEBACK
	&dev_attr_bd_stat.attr,
#endif
	&dev_attr_debug_stat.attr,
#ifdef CONFIG_ZRAM_MULTI_COMP
	&dev_attr_recomp_algorithm.attr,
	&dev_attr_recompress.attr,
#endif
	NULL,
};

static const struct attribute_group zram_disk_attr_group = {
	.attrs = zram_disk_attrs,
};

static const struct attribute_group *zram_disk_attr_groups[] = {
	&zram_disk_attr_group,
	NULL,
};

/*
 * Allocate and initialize new zram device. the function returns
 * '>= 0' device_id upon success, and negative value otherwise.
 */
static int zram_add(void)
{
	struct zram *zram;
	struct request_queue *queue;
	int ret, device_id;

	zram = kzalloc(sizeof(struct zram), GFP_KERNEL);
	if (!zram)
		return -ENOMEM;

	ret = idr_alloc(&zram_index_idr, zram, 0, 0, GFP_KERNEL);
	if (ret < 0)
		goto out_free_dev;
	device_id = ret;

	init_rwsem(&zram->init_lock);
#ifdef CONFIG_ZRAM_WRITEBACK
	zram->wb_batch_size = 32;
	zram->compressed_wb = IS_ENABLED(CONFIG_ZRAM_COMPRESSED_WRITEBACK_DEFAULT);
	spin_lock_init(&zram->wb_limit_lock);
#endif
	queue = blk_alloc_queue(NUMA_NO_NODE);
	if (!queue) {
		pr_err("Error allocating disk queue for device %d\n",
			device_id);
		ret = -ENOMEM;
		goto out_free_idr;
	}

	/* gendisk structure */
	zram->disk = alloc_disk(1);
	if (!zram->disk) {
		pr_err("Error allocating disk structure for device %d\n",
			device_id);
		ret = -ENOMEM;
		goto out_free_queue;
	}

	zram->disk->major = zram_major;
	zram->disk->first_minor = device_id;
	zram->disk->fops = &zram_devops;
	zram->disk->queue = queue;
	zram->disk->private_data = zram;
	snprintf(zram->disk->disk_name, 16, "zram%d", device_id);

	/* Actual capacity set using syfs (/sys/block/zram<id>/disksize */
	set_capacity(zram->disk, 0);
	/* zram devices sort of resembles non-rotational disks */
	blk_queue_flag_set(QUEUE_FLAG_NONROT, zram->disk->queue);
	blk_queue_flag_clear(QUEUE_FLAG_ADD_RANDOM, zram->disk->queue);

	/*
	 * To ensure that we always get PAGE_SIZE aligned
	 * and n*PAGE_SIZED sized I/O requests.
	 */
	blk_queue_physical_block_size(zram->disk->queue, PAGE_SIZE);
	blk_queue_logical_block_size(zram->disk->queue,
					ZRAM_LOGICAL_BLOCK_SIZE);
	blk_queue_io_min(zram->disk->queue, PAGE_SIZE);
	blk_queue_io_opt(zram->disk->queue, PAGE_SIZE);
	zram->disk->queue->limits.discard_granularity = PAGE_SIZE;
	blk_queue_max_discard_sectors(zram->disk->queue, UINT_MAX);
	blk_queue_flag_set(QUEUE_FLAG_DISCARD, zram->disk->queue);

	/*
	 * zram_bio_discard() will clear all logical blocks if logical block
	 * size is identical with physical block size(PAGE_SIZE). But if it is
	 * different, we will skip discarding some parts of logical blocks in
	 * the part of the request range which isn't aligned to physical block
	 * size.  So we can't ensure that all discarded logical blocks are
	 * zeroed.
	 */
	if (ZRAM_LOGICAL_BLOCK_SIZE == PAGE_SIZE)
		blk_queue_max_write_zeroes_sectors(zram->disk->queue, UINT_MAX);

	blk_queue_flag_set(QUEUE_FLAG_STABLE_WRITES, zram->disk->queue);
	device_add_disk(NULL, zram->disk, zram_disk_attr_groups);

	comp_algorithm_set(zram, ZRAM_PRIMARY_COMP, default_compressor);

	zram_debugfs_register(zram);
	pr_info("Added device: %s\n", zram->disk->disk_name);
	return device_id;

out_free_queue:
	blk_cleanup_queue(queue);
out_free_idr:
	idr_remove(&zram_index_idr, device_id);
out_free_dev:
	kfree(zram);
	return ret;
}

static int zram_remove(struct zram *zram)
{
	struct block_device *bdev;

	bdev = bdget_disk(zram->disk, 0);
	if (!bdev)
		return -ENOMEM;

	mutex_lock(&bdev->bd_mutex);
	if (bdev->bd_openers || zram->claim) {
		mutex_unlock(&bdev->bd_mutex);
		bdput(bdev);
		return -EBUSY;
	}

	zram->claim = true;
	mutex_unlock(&bdev->bd_mutex);

	zram_debugfs_unregister(zram);

	/* Make sure all the pending I/O are finished */
	fsync_bdev(bdev);
	zram_reset_device(zram);
	bdput(bdev);

	pr_info("Removed device: %s\n", zram->disk->disk_name);

	del_gendisk(zram->disk);
	blk_cleanup_queue(zram->disk->queue);
	put_disk(zram->disk);
	kfree(zram);
	return 0;
}

/* zram-control sysfs attributes */

/*
 * NOTE: hot_add attribute is not the usual read-only sysfs attribute. In a
 * sense that reading from this file does alter the state of your system -- it
 * creates a new un-initialized zram device and returns back this device's
 * device_id (or an error code if it fails to create a new device).
 */
static ssize_t hot_add_show(struct class *class,
			struct class_attribute *attr,
			char *buf)
{
	int ret;

	mutex_lock(&zram_index_mutex);
	ret = zram_add();
	mutex_unlock(&zram_index_mutex);

	if (ret < 0)
		return ret;
	return scnprintf(buf, PAGE_SIZE, "%d\n", ret);
}
static struct class_attribute class_attr_hot_add =
	__ATTR(hot_add, 0400, hot_add_show, NULL);

static ssize_t hot_remove_store(struct class *class,
			struct class_attribute *attr,
			const char *buf,
			size_t count)
{
	struct zram *zram;
	int ret, dev_id;

	/* dev_id is gendisk->first_minor, which is `int' */
	ret = kstrtoint(buf, 10, &dev_id);
	if (ret)
		return ret;
	if (dev_id < 0)
		return -EINVAL;

	mutex_lock(&zram_index_mutex);

	zram = idr_find(&zram_index_idr, dev_id);
	if (zram) {
		ret = zram_remove(zram);
		if (!ret)
			idr_remove(&zram_index_idr, dev_id);
	} else {
		ret = -ENODEV;
	}

	mutex_unlock(&zram_index_mutex);
	return ret ? ret : count;
}
static CLASS_ATTR_WO(hot_remove);

static struct attribute *zram_control_class_attrs[] = {
	&class_attr_hot_add.attr,
	&class_attr_hot_remove.attr,
	NULL,
};
ATTRIBUTE_GROUPS(zram_control_class);

static struct class zram_control_class = {
	.name		= "zram-control",
	.owner		= THIS_MODULE,
	.class_groups	= zram_control_class_groups,
};

static int zram_remove_cb(int id, void *ptr, void *data)
{
	zram_remove(ptr);
	return 0;
}

static void destroy_devices(void)
{
	class_unregister(&zram_control_class);
	idr_for_each(&zram_index_idr, &zram_remove_cb, NULL);
	zram_debugfs_destroy();
	idr_destroy(&zram_index_idr);
	unregister_blkdev(zram_major, "zram");
	cpuhp_remove_multi_state(CPUHP_ZCOMP_PREPARE);
}

static int __init zram_init(void)
{
	int ret;

	BUILD_BUG_ON(__NR_ZRAM_PAGEFLAGS > BITS_PER_LONG);

	ret = cpuhp_setup_state_multi(CPUHP_ZCOMP_PREPARE, "block/zram:prepare",
				      zcomp_cpu_up_prepare, zcomp_cpu_dead);
	if (ret < 0)
		return ret;

	ret = class_register(&zram_control_class);
	if (ret) {
		pr_err("Unable to register zram-control class\n");
		cpuhp_remove_multi_state(CPUHP_ZCOMP_PREPARE);
		return ret;
	}

	zram_debugfs_create();
	zram_major = register_blkdev(0, "zram");
	if (zram_major <= 0) {
		pr_err("Unable to get major number\n");
		class_unregister(&zram_control_class);
		cpuhp_remove_multi_state(CPUHP_ZCOMP_PREPARE);
		return -EBUSY;
	}

	while (num_devices != 0) {
		mutex_lock(&zram_index_mutex);
		ret = zram_add();
		mutex_unlock(&zram_index_mutex);
		if (ret < 0)
			goto out_error;
		num_devices--;
	}

	return 0;

out_error:
	destroy_devices();
	return ret;
}

static void __exit zram_exit(void)
{
	destroy_devices();
}

module_init(zram_init);
module_exit(zram_exit);

module_param(num_devices, uint, 0);
MODULE_PARM_DESC(num_devices, "Number of pre-created zram devices");

MODULE_LICENSE("Dual BSD/GPL");
MODULE_AUTHOR("Nitin Gupta <ngupta@vflare.org>");
MODULE_DESCRIPTION("Compressed RAM Block Device");
