// author: Miao Yu

#include <xmhf.h>
#include "xmhf-tlsf.h"

static u8 g_xmhf_heap[XMHF_HEAP_SIZE] __attribute__((aligned(PAGE_SIZE_4K)));
static xmhf_tlsf_pool g_pool;

// [Ticket 156][TODO] [SecBase][SecOS] Use Slab + Page Allocator to save memory space

void xmhf_mm_init(void)
{
	g_pool = xmhf_tlsf_create(g_xmhf_heap, XMHF_HEAP_SIZE);
}

void xmhf_mm_fini(void)
{
	if(g_pool)
	{
		xmhf_tlsf_destroy(g_xmhf_heap);
		g_pool = NULL;
	}
}

void* xmhf_mm_malloc_align(uint32_t alignment, size_t size)
{
	void *p = NULL;

	p = xmhf_tlsf_memalign(g_pool, alignment, size);

	if(p)
		memset(p, 0, size);
	return p;
}

void* xmhf_mm_malloc(size_t size)
{
	return xmhf_mm_malloc_align(0, size);
}

void* xmhf_mm_alloc_page(uint32_t num_pages)
{
	return xmhf_mm_malloc_align(PAGE_SIZE_4K, num_pages * PAGE_SIZE_4K);
}


void xmhf_mm_free(void* ptr)
{
	xmhf_tlsf_free(g_pool, ptr);
}

//! Allocate an aligned memory from the heap of XMHF. Also it records the allocation in the <mm_alloc_infolist>
void* xmhf_mm_alloc_align_with_record(XMHFList* mm_alloc_infolist, uint32_t alignment, size_t size)
{
	void* p = NULL;
	struct xmhf_mm_alloc_info* record = NULL;

	if(!mm_alloc_infolist)
		return NULL;

	p = xmhf_mm_malloc_align(alignment, size);
	if(!p)
		return NULL;

	record = xmhf_mm_malloc(sizeof(struct xmhf_mm_alloc_info));
	if(!record)
	{
		xmhf_mm_free(p);
		return NULL;
	}

	record->hva = p;
	record->alignment = alignment;
	record->size = size;
	xmhfstl_list_enqueue(mm_alloc_infolist, record);

	return p;
}

//! Allocate a piece of memory from the heap of XMHF. Also it records the allocation in the <mm_alloc_infolist>
void* xmhf_mm_malloc_with_record(XMHFList* mm_alloc_infolist, size_t size)
{
	return xmhf_mm_alloc_align_with_record(mm_alloc_infolist, 0, size);
}

//! Allocate a memory page from the heap of XMHF. Also it records the allocation in the <mm_alloc_infolist>
void* xmhf_mm_alloc_page_with_record(XMHFList* mm_alloc_infolist, uint32_t num_pages)
{
	return xmhf_mm_alloc_align_with_record(mm_alloc_infolist, PAGE_SIZE_4K, num_pages * PAGE_SIZE_4K);
}

//! Free the memory allocated from the heap of XMHF. And also remove the record in the <mm_alloc_infolist>
void xmhf_mm_free_from_record(XMHFList* mm_alloc_infolist, void* ptr)
{
	// void* p = NULL;
	struct xmhf_mm_alloc_info* record = NULL;
	XMHFListNode* node = NULL;

	if(!mm_alloc_infolist || !ptr)
		return;

	{
		XMHFLIST_FOREACH(mm_alloc_infolist, first, next, cur)
		{
			record = (struct xmhf_mm_alloc_info*)cur->value;

			if(record->hva == ptr)
			{
				node = cur;
				break;
			}
		}
	}

	xmhfstl_list_remove(mm_alloc_infolist, node);

	xmhf_mm_free(record->hva);
	xmhf_mm_free(record);
}

//! @brief Free all the recorded memory
void xmhf_mm_free_all_records(XMHFList* mm_alloc_infolist)
{
	struct xmhf_mm_alloc_info* record = NULL;

	if(!mm_alloc_infolist)
		return;

	{
		XMHFLIST_FOREACH(mm_alloc_infolist, first, next, cur)
		{
			record = (struct xmhf_mm_alloc_info*)cur->value;

			xmhf_mm_free(record->hva);
		}
	}

	xmhfstl_list_clear_destroy(mm_alloc_infolist);
}
