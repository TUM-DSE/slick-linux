// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2012 Red Hat, Inc.  All rights reserved.
 *
 * VFIO container (/dev/vfio/vfio)
 */
#include <linux/file.h>
#include <linux/slab.h>
#include <linux/fs.h>
#include <linux/capability.h>
#include <linux/iommu.h>
#include <linux/miscdevice.h>
#include <linux/vfio.h>
#include <uapi/linux/vfio.h>
#include <linux/set_memory.h>
#include <linux/highmem.h>
#include <linux/mm.h>
#include <linux/dma-map-ops.h>
#include <linux/cma.h>
#include <linux/dma-direct.h>

#include "vfio.h"

struct vfio_container {
	struct kref			kref;
	struct list_head		group_list;
	struct rw_semaphore		group_lock;
	struct vfio_iommu_driver	*iommu_driver;
	void				*iommu_data;
	bool				noiommu;
};

static struct vfio {
	struct list_head		iommu_drivers_list;
	struct mutex			iommu_drivers_lock;
} vfio;

struct vfio_batch {
	struct page		**pages;	/* for pin_user_pages_remote */
	struct page		*fallback_page; /* if pages alloc fails */
	int			capacity;	/* length of pages array */
	int			size;		/* of batch currently */
	int			offset;		/* of next entry in pages */
};

struct vfio_dma {
	struct rb_node		node;
	dma_addr_t		iova;		/* Device address */
	unsigned long		vaddr;		/* Process virtual addr */
	size_t			size;		/* Map size (bytes) */
	int			prot;		/* IOMMU_READ/WRITE */
	bool			iommu_mapped;
	bool			lock_cap;	/* capable(CAP_IPC_LOCK) */
	bool			vaddr_invalid;
	struct task_struct	*task;
	struct rb_root		pfn_list;	/* Ex-user pinned pfn list */
	unsigned long		*bitmap;
	struct mm_struct	*mm;
	size_t			locked_vm;
};

struct vfio_iommu {
	struct list_head	domain_list;
	struct list_head	iova_list;
	struct mutex		lock;
	struct rb_root		dma_list;
	struct list_head	device_list;
	struct mutex		device_list_lock;
	unsigned int		dma_avail;
	unsigned int		vaddr_invalid_count;
	uint64_t		pgsize_bitmap;
	uint64_t		num_non_pinned_groups;
	bool			v2;
	bool			nesting;
	bool			dirty_page_tracking;
	struct list_head	emulated_iommu_groups;
};

/*
 * Guest RAM pinning working set or DMA target
 */
struct vfio_pfn {
	struct rb_node		node;
	dma_addr_t		iova;		/* Device address */
	unsigned long		pfn;		/* Host pfn */
	unsigned int		ref_count;
};

#define VFIO_BATCH_MAX_CAPACITY (PAGE_SIZE / sizeof(struct page *))

static void vfio_batch_fini(struct vfio_batch *batch)
{
	if (batch->capacity == VFIO_BATCH_MAX_CAPACITY)
		free_page((unsigned long)batch->pages);
}

static bool disable_hugepages = false;

/*
 * Helper Functions for host iova-pfn list
 */
static struct vfio_pfn *vfio_find_vpfn(struct vfio_dma *dma, dma_addr_t iova)
{
	struct vfio_pfn *vpfn;
	struct rb_node *node = dma->pfn_list.rb_node;

	while (node) {
		vpfn = rb_entry(node, struct vfio_pfn, node);

		if (iova < vpfn->iova)
			node = node->rb_left;
		else if (iova > vpfn->iova)
			node = node->rb_right;
		else
			return vpfn;
	}
	return NULL;
}

static int mm_lock_acct(struct task_struct *task, struct mm_struct *mm,
			bool lock_cap, long npage)
{
	int ret = mmap_write_lock_killable(mm);

	if (ret)
		return ret;

	ret = __account_locked_vm(mm, abs(npage), npage > 0, task, lock_cap);
	mmap_write_unlock(mm);
	return ret;
}

static int vfio_lock_acct(struct vfio_dma *dma, long npage, bool async)
{
	struct mm_struct *mm;
	int ret;

	if (!npage)
		return 0;

	mm = dma->mm;
	if (async && !mmget_not_zero(mm))
		return -ESRCH; /* process exited */

	ret = mm_lock_acct(dma->task, mm, dma->lock_cap, npage);
	if (!ret)
		dma->locked_vm += npage;

	if (async)
		mmput(mm);

	return ret;
}

/*
 * Some mappings aren't backed by a struct page, for example an mmap'd
 * MMIO range for our own or another device.  These use a different
 * pfn conversion and shouldn't be tracked as locked pages.
 * For compound pages, any driver that sets the reserved bit in head
 * page needs to set the reserved bit in all subpages to be safe.
 */
static bool is_invalid_reserved_pfn(unsigned long pfn)
{
	if (pfn_valid(pfn))
		return PageReserved(pfn_to_page(pfn));

	return true;
}

static int put_pfn(unsigned long pfn, int prot)
{
	if (!is_invalid_reserved_pfn(pfn)) {
		struct page *page = pfn_to_page(pfn);

		unpin_user_pages_dirty_lock(&page, 1, prot & IOMMU_WRITE);
		return 1;
	}
	return 0;
}

static void vfio_batch_init(struct vfio_batch *batch)
{
	batch->size = 0;
	batch->offset = 0;

	if (unlikely(disable_hugepages))
		goto fallback;

	batch->pages = (struct page **) __get_free_page(GFP_KERNEL);
	if (!batch->pages)
		goto fallback;

	batch->capacity = VFIO_BATCH_MAX_CAPACITY;
	return;

fallback:
	batch->pages = &batch->fallback_page;
	batch->capacity = 1;
}

static void vfio_batch_unpin(struct vfio_batch *batch, struct vfio_dma *dma)
{
	while (batch->size) {
		unsigned long pfn = page_to_pfn(batch->pages[batch->offset]);

		put_pfn(pfn, dma->prot);
		batch->offset++;
		batch->size--;
	}
}

static int put_pfn(unsigned long pfn, int prot);

static int follow_fault_pfn(struct vm_area_struct *vma, struct mm_struct *mm,
			    unsigned long vaddr, unsigned long *pfn,
			    bool write_fault)
{
	pte_t *ptep;
	pte_t pte;
	spinlock_t *ptl;
	int ret;

	ret = follow_pte(vma->vm_mm, vaddr, &ptep, &ptl);
	if (ret) {
		bool unlocked = false;

		ret = fixup_user_fault(mm, vaddr,
				       FAULT_FLAG_REMOTE |
				       (write_fault ?  FAULT_FLAG_WRITE : 0),
				       &unlocked);
		if (unlocked)
			return -EAGAIN;

		if (ret)
			return ret;

		ret = follow_pte(vma->vm_mm, vaddr, &ptep, &ptl);
		if (ret)
			return ret;
	}

	pte = ptep_get(ptep);

	if (write_fault && !pte_write(pte))
		ret = -EFAULT;
	else
		*pfn = pte_pfn(pte);

	pte_unmap_unlock(ptep, ptl);
	return ret;
}
/*
 * Returns the positive number of pfns successfully obtained or a negative
 * error code.
 */
static int vaddr_get_pfns(struct mm_struct *mm, unsigned long vaddr,
			  long npages, int prot, unsigned long *pfn,
			  struct page **pages)
{
	struct vm_area_struct *vma;
	unsigned int flags = 0;
	int ret;

	if (prot & IOMMU_WRITE)
		flags |= FOLL_WRITE;

	mmap_read_lock(mm);
	ret = pin_user_pages_remote(mm, vaddr, npages, flags | FOLL_LONGTERM,
				    pages, NULL);
	if (ret > 0) {
		int i;

		/*
		 * The zero page is always resident, we don't need to pin it
		 * and it falls into our invalid/reserved test so we don't
		 * unpin in put_pfn().  Unpin all zero pages in the batch here.
		 */
		for (i = 0 ; i < ret; i++) {
			if (unlikely(is_zero_pfn(page_to_pfn(pages[i]))))
				unpin_user_page(pages[i]);
		}

		*pfn = page_to_pfn(pages[0]);
		goto done;
	}

	vaddr = untagged_addr_remote(mm, vaddr);

retry:
	vma = vma_lookup(mm, vaddr);

	if (vma && vma->vm_flags & VM_PFNMAP) {
		ret = follow_fault_pfn(vma, mm, vaddr, pfn, prot & IOMMU_WRITE);
		if (ret == -EAGAIN)
			goto retry;

		if (!ret) {
			if (is_invalid_reserved_pfn(*pfn))
				ret = 1;
			else
				ret = -EFAULT;
		}
	}
done:
	mmap_read_unlock(mm);
	return ret;
}

/*
 * Attempt to pin pages.  We really don't want to track all the pfns and
 * the iommu can only map chunks of consecutive pfns anyway, so get the
 * first page and all consecutive pages with the same locking.
 */
static long vfio_pin_pages_remote(struct vfio_dma *dma, unsigned long vaddr,
				  long npage, unsigned long *pfn_base,
				  unsigned long limit, struct vfio_batch *batch)
{
	unsigned long pfn;
	struct mm_struct *mm = current->mm;
	long ret, pinned = 0, lock_acct = 0;
	bool rsvd;
	dma_addr_t iova = vaddr - dma->vaddr + dma->iova;

	/* This code path is only user initiated */
	if (!mm)
		return -ENODEV;

	pr_err("foobar8.1\n");
	if (batch->size) {
		/* Leftover pages in batch from an earlier call. */
		*pfn_base = page_to_pfn(batch->pages[batch->offset]);
		pfn = *pfn_base;
		rsvd = is_invalid_reserved_pfn(*pfn_base);
	} else {
		*pfn_base = 0;
	}

	while (npage) {
		pr_err("foobar8.2\n");
		if (!batch->size) {
			/* Empty batch, so refill it. */
			long req_pages = min_t(long, npage, batch->capacity);

			ret = vaddr_get_pfns(mm, vaddr, req_pages, dma->prot,
					     &pfn, batch->pages);
			if (ret < 0)
				goto unpin_out;

			batch->size = ret;
			batch->offset = 0;

			if (!*pfn_base) {
				*pfn_base = pfn;
				rsvd = is_invalid_reserved_pfn(*pfn_base);
			}
		}

		/*
		 * pfn is preset for the first iteration of this inner loop and
		 * updated at the end to handle a VM_PFNMAP pfn.  In that case,
		 * batch->pages isn't valid (there's no struct page), so allow
		 * batch->pages to be touched only when there's more than one
		 * pfn to check, which guarantees the pfns are from a
		 * !VM_PFNMAP vma.
		 */
		pr_err("foobar8.3\n");
		while (true) {
			if (pfn != *pfn_base + pinned ||
			    rsvd != is_invalid_reserved_pfn(pfn))
				goto out;

			/*
			 * Reserved pages aren't counted against the user,
			 * externally pinned pages are already counted against
			 * the user.
			 */
			//if (!rsvd && !vfio_find_vpfn(dma, iova)) {
			//	if (!dma->lock_cap &&
			//	    mm->locked_vm + lock_acct + 1 > limit) {
			//		pr_warn("%s: RLIMIT_MEMLOCK (%ld) exceeded\n",
			//			__func__, limit << PAGE_SHIFT);
			//		ret = -ENOMEM;
			//		goto unpin_out;
			//	}
			//	lock_acct++;
			//}

			pinned++;
			npage--;
			vaddr += PAGE_SIZE;
			iova += PAGE_SIZE;
			batch->offset++;
			batch->size--;

			if (!batch->size)
				break;

			pr_err("foobar8.4\n");
			pfn = page_to_pfn(batch->pages[batch->offset]);
		}

		if (unlikely(disable_hugepages))
			break;
	}

	pr_err("foobar8.5\n");
out:
	/* ret = vfio_lock_acct(dma, lock_acct, false); */

unpin_out:
	if (batch->size == 1 && !batch->offset) {
		/* May be a VM_PFNMAP pfn, which the batch can't remember. */
		put_pfn(pfn, dma->prot);
		batch->size = 0;
	}

	if (ret < 0) {
		if (pinned && !rsvd) {
			for (pfn = *pfn_base ; pinned ; pfn++, pinned--)
				put_pfn(pfn, dma->prot);
		}
		vfio_batch_unpin(batch, dma);

		return ret;
	}

	return pinned;
}
static int vfio_cvm_dma_do_map(struct vfio_iommu *iommu,
			   struct vfio_iommu_type1_dma_map *map)
{
	pr_err("foobar7\n");
	bool set_vaddr = map->flags & VFIO_DMA_MAP_FLAG_VADDR;
	dma_addr_t iova = map->iova;
	unsigned long vaddr = map->vaddr;
	size_t size = map->size;
	int ret = 0, prot = 0;
	size_t pgsize;
	struct vfio_dma dma;
	dma.vaddr = vaddr;
	dma.iova = iova;
	dma.size = size;

	/* Verify that none of our __u64 fields overflow */
	if (map->size != size || map->vaddr != vaddr || map->iova != iova)
		return -EINVAL;

	/* READ/WRITE from device perspective */
	if (map->flags & VFIO_DMA_MAP_FLAG_WRITE)
		prot |= IOMMU_WRITE;
	if (map->flags & VFIO_DMA_MAP_FLAG_READ)
		prot |= IOMMU_READ;

	if ((prot && set_vaddr) || (!prot && !set_vaddr))
		return -EINVAL;

	// TODO we completely repurpose VFIO for decrypting pages in AMD SEV-SNP, because we don't need VFIO with IOMMU anyways.
	// current->mm can be used to resolve user addresses (vfio_iommu_type1.c:641)
	unsigned int npages = PAGE_ALIGN(size) >> PAGE_SHIFT;
	unsigned long limit = rlimit(RLIMIT_MEMLOCK) >> PAGE_SHIFT;

	unsigned long pfn_base = 0;
	struct vfio_batch batch;

	/* mutex_lock(&iommu->lock); */
	vfio_batch_init(&batch);

	pr_err("foobar8\n");
	/* Pin a contiguous chunk of memory */
	unsigned int npage = vfio_pin_pages_remote(&dma, vaddr + dma.size,
					    size >> PAGE_SHIFT, &pfn_base, limit,
					    &batch);
	if (npage <= 0) {
		WARN_ON(!npage);
		ret = (int)npage;
		goto out_unlock;
	}

	pr_err("foobar9\n");
	// TODO for each batch->page
		void* kaddr = kmap(batch.pages[0]);

	pr_err("foobar10\n");
		ret = set_memory_decrypted(kaddr, 1); // num pages 1
		if (ret) {
			pr_err("failed to decrypt page %p, ret=%d\n",
							kaddr, ret);
			ret = -1;
			goto out_unlock;
		}
			pr_err("decrypt page %p at userspace %ld, ret=%d\n",
							kaddr, vaddr, ret);

	// TODO kunmap


	// TODO esure that pages are unpinned again (put_page?)

out_unlock:
	pr_err("foobar11\n");
	vfio_batch_fini(&batch);

	/* mutex_unlock(&iommu->lock); */
	return ret;
}

static bool cma_in_zone(gfp_t gfp)
{
	unsigned long size;
	phys_addr_t end;
	struct cma *cma;

	cma = dev_get_cma_area(NULL);
	if (!cma)
		return false;

	size = cma_get_size(cma);
	if (!size)
		return false;

	/* CMA can't cross zone boundaries, see cma_activate_area() */
	end = cma_get_base(cma) + size - 1;
	if (IS_ENABLED(CONFIG_ZONE_DMA) && (gfp & GFP_DMA))
		return end <= DMA_BIT_MASK(zone_dma_bits);
	if (IS_ENABLED(CONFIG_ZONE_DMA32) && (gfp & GFP_DMA32))
		return end <= DMA_BIT_MASK(32);
	return true;
}
static int hacky_atomic_pool_expand(size_t pool_size)
{
	pr_err("fizz1\n");
	gfp_t gfp;
	if (IS_ENABLED(CONFIG_ZONE_DMA))
		gfp = GFP_KERNEL | GFP_DMA;
	else
		gfp = GFP_KERNEL;

	unsigned int order;
	struct page *page = NULL;
	void *addr;
	int ret = -ENOMEM;

	/* Cannot allocate larger than MAX_ORDER */
	order = min(get_order(pool_size), MAX_ORDER);

	do {
		pool_size = 1 << (PAGE_SHIFT + order);
		if (cma_in_zone(gfp))
			page = dma_alloc_from_contiguous(NULL, 1 << order,
							 order, false);
		if (!page)
			page = alloc_pages(gfp, order);
	} while (!page && order-- > 0);
	if (!page)
		goto out;

	arch_dma_prep_coherent(page, pool_size);

#ifdef CONFIG_DMA_DIRECT_REMAP
	addr = dma_common_contiguous_remap(page, pool_size,
					   pgprot_dmacoherent(PAGE_KERNEL),
					   __builtin_return_address(0));
	if (!addr)
		goto free_page;
#else
	addr = page_to_virt(page);
#endif
	/*
	 * Memory in the atomic DMA pools must be unencrypted, the pools do not
	 * shrink so no re-encryption occurs in dma_direct_free().
	 */
	ret = set_memory_decrypted((unsigned long)page_to_virt(page),
				   1 << order);
	if (ret)
		goto remove_mapping;
	/* ret = gen_pool_add_virt(pool, (unsigned long)addr, page_to_phys(page), */
	/* 			pool_size, NUMA_NO_NODE); */
	/* if (ret) */
	/* 	goto encrypt_mapping; */

	/* dma_atomic_pool_size_add(gfp, pool_size); */
	pr_err("fizz heureka1 virt %p phys %ld, %ld\n", addr, page_to_pfn(page), (page_to_pfn(page))*PAGE_SIZE);
	*((uint32_t*)addr) = 0x1337;
	pr_err("u32: %d\n", *((uint32_t*)addr));
	return 0;

encrypt_mapping:
	//ret = set_memory_encrypted((unsigned long)page_to_virt(page),
	//			   1 << order);
	//if (WARN_ON_ONCE(ret)) {
	//	/* Decrypt succeeded but encrypt failed, purposely leak */
	//	goto out;
	//}
remove_mapping:
//#ifdef CONFIG_DMA_DIRECT_REMAP
//	dma_common_free_remap(addr, pool_size);
//#endif
free_page: __maybe_unused
	__free_pages(page, order);
out:
	return ret;
}

static int vfio_cvm_map_dma(struct vfio_iommu *iommu,
				    unsigned long arg)
{
	pr_err("foobar5\n");
	struct vfio_iommu_type1_dma_map map;
	unsigned long minsz;
	uint32_t mask = VFIO_DMA_MAP_FLAG_READ | VFIO_DMA_MAP_FLAG_WRITE |
			VFIO_DMA_MAP_FLAG_VADDR;

	minsz = offsetofend(struct vfio_iommu_type1_dma_map, size);

	pr_err("foobar6\n");
	if (copy_from_user(&map, (void __user *)arg, minsz))
		return -EFAULT;

	if (map.argsz < minsz || map.flags & ~mask)
		return -EINVAL;
	return hacky_atomic_pool_expand(map.size);
	/* return vfio_cvm_dma_do_map(iommu, &map); */
}

static unsigned int dma_entry_limit __read_mostly = U16_MAX;

static void *vfio_noiommu_open(unsigned long arg)
{
	/* struct vfio_iommu *iommu; */
	/* iommu = kzalloc(sizeof(*iommu), GFP_KERNEL); */
	/* if (!iommu) */
	/* 	return ERR_PTR(-ENOMEM); */
	/**/
	/* INIT_LIST_HEAD(&iommu->domain_list); */
	/* INIT_LIST_HEAD(&iommu->iova_list); */
	/* iommu->dma_list = RB_ROOT; */
	/* iommu->dma_avail = dma_entry_limit; */
	/* mutex_init(&iommu->lock); */
	/* mutex_init(&iommu->device_list_lock); */
	/* INIT_LIST_HEAD(&iommu->device_list); */
	/* iommu->pgsize_bitmap = PAGE_MASK; */
	/* INIT_LIST_HEAD(&iommu->emulated_iommu_groups); */
	/**/
	if (arg != VFIO_NOIOMMU_IOMMU)
		return ERR_PTR(-EINVAL);
	if (!capable(CAP_SYS_RAWIO))
		return ERR_PTR(-EPERM);

	return NULL;
	/* return iommu; */
}


static void vfio_noiommu_release(void *iommu_data)
{
}

static long vfio_noiommu_ioctl(void *iommu_data,
			       unsigned int cmd, unsigned long arg)
{
	pr_err("foobar\n");
	/* struct vfio_iommu *iommu = iommu_data; // TODO never lol */

	switch (cmd) {
	case VFIO_CHECK_EXTENSION:
		return vfio_noiommu && (arg == VFIO_NOIOMMU_IOMMU) ? 1 : 0;
	case VFIO_IOMMU_MAP_DMA:
		/* return vfio_cvm_map_dma(iommu, arg); */
		return vfio_cvm_map_dma(NULL, arg);
	default:
		return -ENOTTY;
	}

	return -ENOTTY;
}

static int vfio_noiommu_attach_group(void *iommu_data,
		struct iommu_group *iommu_group, enum vfio_group_type type)
{
	return 0;
}

static void vfio_noiommu_detach_group(void *iommu_data,
				      struct iommu_group *iommu_group)
{
}

static const struct vfio_iommu_driver_ops vfio_noiommu_ops = {
	.name = "vfio-noiommu",
	.owner = THIS_MODULE,
	.open = vfio_noiommu_open,
	.release = vfio_noiommu_release,
	.ioctl = vfio_noiommu_ioctl,
	/* .ioctl = vfio_iommu_type1_ioctl, */
	.attach_group = vfio_noiommu_attach_group,
	.detach_group = vfio_noiommu_detach_group,
};

/*
 * Only noiommu containers can use vfio-noiommu and noiommu containers can only
 * use vfio-noiommu.
 */
static bool vfio_iommu_driver_allowed(struct vfio_container *container,
				      const struct vfio_iommu_driver *driver)
{
	if (!IS_ENABLED(CONFIG_VFIO_NOIOMMU))
		return true;
	return container->noiommu == (driver->ops == &vfio_noiommu_ops);
}

/*
 * IOMMU driver registration
 */
int vfio_register_iommu_driver(const struct vfio_iommu_driver_ops *ops)
{
	struct vfio_iommu_driver *driver, *tmp;

	if (WARN_ON(!ops->register_device != !ops->unregister_device))
		return -EINVAL;

	driver = kzalloc(sizeof(*driver), GFP_KERNEL);
	if (!driver)
		return -ENOMEM;

	driver->ops = ops;

	mutex_lock(&vfio.iommu_drivers_lock);

	/* Check for duplicates */
	list_for_each_entry(tmp, &vfio.iommu_drivers_list, vfio_next) {
		if (tmp->ops == ops) {
			mutex_unlock(&vfio.iommu_drivers_lock);
			kfree(driver);
			return -EINVAL;
		}
	}

	list_add(&driver->vfio_next, &vfio.iommu_drivers_list);

	mutex_unlock(&vfio.iommu_drivers_lock);

	return 0;
}
EXPORT_SYMBOL_GPL(vfio_register_iommu_driver);

void vfio_unregister_iommu_driver(const struct vfio_iommu_driver_ops *ops)
{
	struct vfio_iommu_driver *driver;

	mutex_lock(&vfio.iommu_drivers_lock);
	list_for_each_entry(driver, &vfio.iommu_drivers_list, vfio_next) {
		if (driver->ops == ops) {
			list_del(&driver->vfio_next);
			mutex_unlock(&vfio.iommu_drivers_lock);
			kfree(driver);
			return;
		}
	}
	mutex_unlock(&vfio.iommu_drivers_lock);
}
EXPORT_SYMBOL_GPL(vfio_unregister_iommu_driver);

/*
 * Container objects - containers are created when /dev/vfio/vfio is
 * opened, but their lifecycle extends until the last user is done, so
 * it's freed via kref.  Must support container/group/device being
 * closed in any order.
 */
static void vfio_container_release(struct kref *kref)
{
	struct vfio_container *container;
	container = container_of(kref, struct vfio_container, kref);

	kfree(container);
}

static void vfio_container_get(struct vfio_container *container)
{
	kref_get(&container->kref);
}

static void vfio_container_put(struct vfio_container *container)
{
	kref_put(&container->kref, vfio_container_release);
}

void vfio_device_container_register(struct vfio_device *device)
{
	struct vfio_iommu_driver *iommu_driver =
		device->group->container->iommu_driver;

	if (iommu_driver && iommu_driver->ops->register_device)
		iommu_driver->ops->register_device(
			device->group->container->iommu_data, device);
}

void vfio_device_container_unregister(struct vfio_device *device)
{
	struct vfio_iommu_driver *iommu_driver =
		device->group->container->iommu_driver;

	if (iommu_driver && iommu_driver->ops->unregister_device)
		iommu_driver->ops->unregister_device(
			device->group->container->iommu_data, device);
}

static long
vfio_container_ioctl_check_extension(struct vfio_container *container,
				     unsigned long arg)
{
	struct vfio_iommu_driver *driver;
	long ret = 0;

	down_read(&container->group_lock);

	driver = container->iommu_driver;

	switch (arg) {
		/* No base extensions yet */
	default:
		/*
		 * If no driver is set, poll all registered drivers for
		 * extensions and return the first positive result.  If
		 * a driver is already set, further queries will be passed
		 * only to that driver.
		 */
		if (!driver) {
			mutex_lock(&vfio.iommu_drivers_lock);
			list_for_each_entry(driver, &vfio.iommu_drivers_list,
					    vfio_next) {

				if (!list_empty(&container->group_list) &&
				    !vfio_iommu_driver_allowed(container,
							       driver))
					continue;
				if (!try_module_get(driver->ops->owner))
					continue;

				ret = driver->ops->ioctl(NULL,
							 VFIO_CHECK_EXTENSION,
							 arg);
				module_put(driver->ops->owner);
				if (ret > 0)
					break;
			}
			mutex_unlock(&vfio.iommu_drivers_lock);
		} else
			ret = driver->ops->ioctl(container->iommu_data,
						 VFIO_CHECK_EXTENSION, arg);
	}

	up_read(&container->group_lock);

	return ret;
}

/* hold write lock on container->group_lock */
static int __vfio_container_attach_groups(struct vfio_container *container,
					  struct vfio_iommu_driver *driver,
					  void *data)
{
	struct vfio_group *group;
	int ret = -ENODEV;

	list_for_each_entry(group, &container->group_list, container_next) {
		ret = driver->ops->attach_group(data, group->iommu_group,
						group->type);
		if (ret)
			goto unwind;
	}

	return ret;

unwind:
	list_for_each_entry_continue_reverse(group, &container->group_list,
					     container_next) {
		driver->ops->detach_group(data, group->iommu_group);
	}

	return ret;
}

static long vfio_ioctl_set_iommu(struct vfio_container *container,
				 unsigned long arg)
{
	struct vfio_iommu_driver *driver;
	long ret = -ENODEV;
	pr_err("foobar2\n");

	down_write(&container->group_lock);

	/*
	 * The container is designed to be an unprivileged interface while
	 * the group can be assigned to specific users.  Therefore, only by
	 * adding a group to a container does the user get the privilege of
	 * enabling the iommu, which may allocate finite resources.  There
	 * is no unset_iommu, but by removing all the groups from a container,
	 * the container is deprivileged and returns to an unset state.
	 */
	if (list_empty(&container->group_list) || container->iommu_driver) {
		up_write(&container->group_lock);
		return -EINVAL;
	}

	mutex_lock(&vfio.iommu_drivers_lock);
	list_for_each_entry(driver, &vfio.iommu_drivers_list, vfio_next) {
		void *data;

		if (!vfio_iommu_driver_allowed(container, driver))
			continue;
		if (!try_module_get(driver->ops->owner))
			continue;

		/*
		 * The arg magic for SET_IOMMU is the same as CHECK_EXTENSION,
		 * so test which iommu driver reported support for this
		 * extension and call open on them.  We also pass them the
		 * magic, allowing a single driver to support multiple
		 * interfaces if they'd like.
		 */
		if (driver->ops->ioctl(NULL, VFIO_CHECK_EXTENSION, arg) <= 0) {
			module_put(driver->ops->owner);
			continue;
		}

		data = driver->ops->open(arg);
		if (IS_ERR(data)) {
			ret = PTR_ERR(data);
			module_put(driver->ops->owner);
			continue;
		}

		ret = __vfio_container_attach_groups(container, driver, data);
		if (ret) {
			driver->ops->release(data);
			module_put(driver->ops->owner);
			continue;
		}

		container->iommu_driver = driver;
		container->iommu_data = data;
		break;
	}

	mutex_unlock(&vfio.iommu_drivers_lock);
	up_write(&container->group_lock);

	return ret;
}

static long vfio_fops_unl_ioctl(struct file *filep,
				unsigned int cmd, unsigned long arg)
{
	pr_err("foobar3\n");
	struct vfio_container *container = filep->private_data;
	struct vfio_iommu_driver *driver;
	void *data;
	long ret = -EINVAL;

	if (!container)
		return ret;

	switch (cmd) {
	case VFIO_GET_API_VERSION:
		ret = VFIO_API_VERSION;
		break;
	case VFIO_CHECK_EXTENSION:
		ret = vfio_container_ioctl_check_extension(container, arg);
		break;
	case VFIO_SET_IOMMU:
		ret = vfio_ioctl_set_iommu(container, arg);
		break;
	default:
		driver = container->iommu_driver;
		data = container->iommu_data;

		if (driver) /* passthrough all unrecognized ioctls */
			ret = driver->ops->ioctl(data, cmd, arg);
	}

	return ret;
}

static int vfio_fops_open(struct inode *inode, struct file *filep)
{
	struct vfio_container *container;

	container = kzalloc(sizeof(*container), GFP_KERNEL_ACCOUNT);
	if (!container)
		return -ENOMEM;

	INIT_LIST_HEAD(&container->group_list);
	init_rwsem(&container->group_lock);
	kref_init(&container->kref);

	filep->private_data = container;

	return 0;
}

static int vfio_fops_release(struct inode *inode, struct file *filep)
{
	struct vfio_container *container = filep->private_data;

	filep->private_data = NULL;

	vfio_container_put(container);

	return 0;
}

static const struct file_operations vfio_fops = {
	.owner		= THIS_MODULE,
	.open		= vfio_fops_open,
	.release	= vfio_fops_release,
	.unlocked_ioctl	= vfio_fops_unl_ioctl,
	.compat_ioctl	= compat_ptr_ioctl,
};

struct vfio_container *vfio_container_from_file(struct file *file)
{
	struct vfio_container *container;

	/* Sanity check, is this really our fd? */
	if (file->f_op != &vfio_fops)
		return NULL;

	container = file->private_data;
	WARN_ON(!container); /* fget ensures we don't race vfio_release */
	return container;
}

static struct miscdevice vfio_dev = {
	.minor = VFIO_MINOR,
	.name = "vfio",
	.fops = &vfio_fops,
	.nodename = "vfio/vfio",
	.mode = S_IRUGO | S_IWUGO,
};

int vfio_container_attach_group(struct vfio_container *container,
				struct vfio_group *group)
{
	struct vfio_iommu_driver *driver;
	int ret = 0;

	lockdep_assert_held(&group->group_lock);

	if (group->type == VFIO_NO_IOMMU && !capable(CAP_SYS_RAWIO))
		return -EPERM;

	down_write(&container->group_lock);

	/* Real groups and fake groups cannot mix */
	if (!list_empty(&container->group_list) &&
	    container->noiommu != (group->type == VFIO_NO_IOMMU)) {
		ret = -EPERM;
		goto out_unlock_container;
	}

	if (group->type == VFIO_IOMMU) {
		ret = iommu_group_claim_dma_owner(group->iommu_group, group);
		if (ret)
			goto out_unlock_container;
	}

	driver = container->iommu_driver;
	if (driver) {
		ret = driver->ops->attach_group(container->iommu_data,
						group->iommu_group,
						group->type);
		if (ret) {
			if (group->type == VFIO_IOMMU)
				iommu_group_release_dma_owner(
					group->iommu_group);
			goto out_unlock_container;
		}
	}

	group->container = container;
	group->container_users = 1;
	container->noiommu = (group->type == VFIO_NO_IOMMU);
	list_add(&group->container_next, &container->group_list);

	/* Get a reference on the container and mark a user within the group */
	vfio_container_get(container);

out_unlock_container:
	up_write(&container->group_lock);
	return ret;
}

void vfio_group_detach_container(struct vfio_group *group)
{
	struct vfio_container *container = group->container;
	struct vfio_iommu_driver *driver;

	lockdep_assert_held(&group->group_lock);
	WARN_ON(group->container_users != 1);

	down_write(&container->group_lock);

	driver = container->iommu_driver;
	if (driver)
		driver->ops->detach_group(container->iommu_data,
					  group->iommu_group);

	if (group->type == VFIO_IOMMU)
		iommu_group_release_dma_owner(group->iommu_group);

	group->container = NULL;
	group->container_users = 0;
	list_del(&group->container_next);

	/* Detaching the last group deprivileges a container, remove iommu */
	if (driver && list_empty(&container->group_list)) {
		driver->ops->release(container->iommu_data);
		module_put(driver->ops->owner);
		container->iommu_driver = NULL;
		container->iommu_data = NULL;
	}

	up_write(&container->group_lock);

	vfio_container_put(container);
}

int vfio_group_use_container(struct vfio_group *group)
{
	lockdep_assert_held(&group->group_lock);

	/*
	 * The container fd has been assigned with VFIO_GROUP_SET_CONTAINER but
	 * VFIO_SET_IOMMU hasn't been done yet.
	 */
	if (!group->container->iommu_driver)
		return -EINVAL;

	if (group->type == VFIO_NO_IOMMU && !capable(CAP_SYS_RAWIO))
		return -EPERM;

	get_file(group->opened_file);
	group->container_users++;
	return 0;
}

void vfio_group_unuse_container(struct vfio_group *group)
{
	lockdep_assert_held(&group->group_lock);

	WARN_ON(group->container_users <= 1);
	group->container_users--;
	fput(group->opened_file);
}

int vfio_device_container_pin_pages(struct vfio_device *device,
				    dma_addr_t iova, int npage,
				    int prot, struct page **pages)
{
	struct vfio_container *container = device->group->container;
	struct iommu_group *iommu_group = device->group->iommu_group;
	struct vfio_iommu_driver *driver = container->iommu_driver;

	if (npage > VFIO_PIN_PAGES_MAX_ENTRIES)
		return -E2BIG;

	if (unlikely(!driver || !driver->ops->pin_pages))
		return -ENOTTY;
	return driver->ops->pin_pages(container->iommu_data, iommu_group, iova,
				      npage, prot, pages);
}

void vfio_device_container_unpin_pages(struct vfio_device *device,
				       dma_addr_t iova, int npage)
{
	struct vfio_container *container = device->group->container;

	if (WARN_ON(npage <= 0 || npage > VFIO_PIN_PAGES_MAX_ENTRIES))
		return;

	container->iommu_driver->ops->unpin_pages(container->iommu_data, iova,
						  npage);
}

int vfio_device_container_dma_rw(struct vfio_device *device,
				 dma_addr_t iova, void *data,
				 size_t len, bool write)
{
	struct vfio_container *container = device->group->container;
	struct vfio_iommu_driver *driver = container->iommu_driver;

	if (unlikely(!driver || !driver->ops->dma_rw))
		return -ENOTTY;
	return driver->ops->dma_rw(container->iommu_data, iova, data, len,
				   write);
}

int __init vfio_container_init(void)
{
	int ret;

	mutex_init(&vfio.iommu_drivers_lock);
	INIT_LIST_HEAD(&vfio.iommu_drivers_list);

	ret = misc_register(&vfio_dev);
	if (ret) {
		pr_err("vfio: misc device register failed\n");
		return ret;
	}

	if (IS_ENABLED(CONFIG_VFIO_NOIOMMU)) {
		ret = vfio_register_iommu_driver(&vfio_noiommu_ops);
		if (ret)
			goto err_misc;
	}
	return 0;

err_misc:
	misc_deregister(&vfio_dev);
	return ret;
}

void vfio_container_cleanup(void)
{
	if (IS_ENABLED(CONFIG_VFIO_NOIOMMU))
		vfio_unregister_iommu_driver(&vfio_noiommu_ops);
	misc_deregister(&vfio_dev);
	mutex_destroy(&vfio.iommu_drivers_lock);
}

MODULE_ALIAS_MISCDEV(VFIO_MINOR);
MODULE_ALIAS("devname:vfio/vfio");
