//hardware_paging.h 
//definitions for intel extended page tables
//author: amit vasudevan (amitvasudevan@acm.org)
#ifndef _HARDWARE_PAGING_H_
#define _HARDWARE_PAGING_H_

extern u32 __ept_pml4_table[];
extern u32 __ept_pdp_table[];
extern u32 __ept_pd_tables[];
extern u32 __ept_p_tables[];

void vmx_setupEPT(void);
void dumpmtrr(void);

#endif // __HARDWARE_PAGING_H_
