/*
	DMA protection module definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __DMAPROT_H__
#define __DMAPROT_H__


#ifndef __ASSEMBLY__

#define dmapa_to_syspa(x) (x & 0x3FFFFFFFUL)
#define syspa_to_dmapa(x) (x | 0xC0000000UL)

typedef struct {
	arm8_32_regs_t *r;
	u32 va;
	u32 pa;
	u32 sas;
	u32 srt;
	u32 wnr;
	u32 il;
} info_intercept_data_abort_t;


typedef struct {
	u32 ti;
	u32 src_addr;
	u32 dst_addr;
	u32 len;
	u32 stride;
	u32 next_cb_addr;
	u32 rsv_0;
	u32 rsv_1;
} dmac_cb_t;


void dmaprot_activate(void);

void dmaprot_handle_dmacontroller_access(info_intercept_data_abort_t *ida);

void dmaprot_handle_usbdmac_access(info_intercept_data_abort_t *ida);


#endif // __ASSEMBLY__



#endif //__DMAPROT_H__
