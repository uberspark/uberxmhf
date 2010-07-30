//shadow_paging.h 
//definitions for shadow paging (non-PAE)
//author: amit vasudevan (amitvasudevan@acm.org)
#ifndef _SHADOW_PAGING_NPAE_H_
#define _SHADOW_PAGING_NPAE_H_

//extern u32 __shadow_pdp_table[];
//extern u32 __shadow_pd_tables[];
//extern u32 __shadow_p_tables[];

extern u32 __shadow_npae_pd_table[];
extern u32 __shadow_npae_p_tables[];

extern u32 shadow_guest_CR3;

u32 shadow_page_fault(u32 cr2, u32 error_code);
void shadow_invalidate_page(u32 address);
u32 shadow_new_context(u32 guest_CR3);
//void shadow_copy(u32 gCR3);
u32 shadow_checkcontext(u32 root);

//guest physical address to host physical address, we have it
//unity mapped for our hypervisor. ie, gpa = hpa
#define gpa_to_hpa(x)	x

#define PFERR_PRESENT_MASK (1U << 0)
#define PFERR_WR_MASK (1U << 1)
#define PFERR_US_MASK (1U << 2)
#define PFERR_RSVD_MASK (1U << 3)
#define PFERR_ID_MASK (1U << 4)

//masks for AVL bits that we use
#define _PAGE_SHADOW_DIRTYWAITING		0x200	
#define _PAGE_SHADOW_ORIGINALRWBIT	0x400
#define _PAGE_SHADOW_UNUSEDAVL			0x800


#endif // __SHADOW_PAGING_NPAE_H_
