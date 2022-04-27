// author: Miao Yu
#ifndef __XMHF_MM_H__
#define __XMHF_MM_H__

#define XMHF_HEAP_SIZE	(64*(1<<20))
#ifndef __ASSEMBLY__

//! This struct records the information of memory allocation
//! This struct is stored in the caller provided memory allocation record list.
struct xmhf_mm_alloc_info
{
	void* 		hva;
	uint32_t 	alignment;
	size_t 		size;
};

void xmhf_mm_init(void);
void xmhf_mm_fini(void);
void* xmhf_mm_alloc_page(uint32_t num_pages);
void* xmhf_mm_malloc(size_t size);
void* xmhf_mm_malloc_align(uint32_t alignment, size_t size);
void xmhf_mm_free(void* ptr);

//! Allocate an aligned memory from the heap of XMHF. Also it records the allocation in the <mm_alloc_infolist>
extern void* xmhf_mm_alloc_align_with_record(XMHFList* mm_alloc_infolist, uint32_t alignment, size_t size);

//! Allocate a piece of memory from the heap of XMHF. Also it records the allocation in the <mm_alloc_infolist>
extern void* xmhf_mm_malloc_with_record(XMHFList* mm_alloc_infolist, size_t size);

//! Allocate a memory page from the heap of XMHF. Also it records the allocation in the <mm_alloc_infolist>
extern void* xmhf_mm_alloc_page_with_record(XMHFList* mm_alloc_infolist, uint32_t num_pages);

//! Free the memory allocated from the heap of XMHF. And also remove the record in the <mm_alloc_infolist>
extern void xmhf_mm_free_from_record(XMHFList* mm_alloc_infolist, void* ptr);

//! @brief Free all the recorded memory
extern void xmhf_mm_free_all_records(XMHFList* mm_alloc_infolist);


#endif // __ASSEMBLY__

#endif // __XMHF_MM_H__
