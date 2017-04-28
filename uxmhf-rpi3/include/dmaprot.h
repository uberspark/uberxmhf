/*
	DMA protection module definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __DMAPROT_H__
#define __DMAPROT_H__


#ifndef __ASSEMBLY__

typedef struct {
	arm8_32_regs_t *r;
	u32 va;
	u32 pa;
	u32 sas;
	u32 srt;
	u32 wnr;
	u32 il;
} info_intercept_data_abort_t;

void dmaprot_activate(void);

void dmaprot_handle_dmacontroller_access(info_intercept_data_abort_t *ida);


#endif // __ASSEMBLY__



#endif //__DMAPROT_H__
