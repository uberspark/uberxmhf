/*
	Pi3 DMA protection implementation

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>
#include <dmaprot.h>

//activate DMA protection mechanism
void dmaprot_activate(void){
	u64 attrs_dev = (LDESC_S2_MC_DEVnGnRnE << LDESC_S2_MEMATTR_MC_SHIFT) |
			(LDESC_S2_S2AP_NO_ACCESS << LDESC_S2_MEMATTR_S2AP_SHIFT) |
			(MEM_INNER_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
			LDESC_S2_MEMATTR_AF_MASK;

	uapi_s2pgtbl_setprot(BCM2837_DMA0_REGS_BASE, attrs_dev);
	sysreg_tlbiallis();
	uapi_s2pgtbl_setprot(BCM2837_DMA15_REGS_BASE, attrs_dev);
	sysreg_tlbiallis();
}


void dmaprot_sanitizecb(u32 cb_pa){
	u32 cb_syspa = dmapa_to_syspa(cb_pa);

	_XDPRINTFSMP_("%s: cb_pa=0x%08x, cb_syspa=0x%08x\n", __func__, cb_pa, cb_syspa);
	_XDPRINTFSMP_("%s: Halting!\n", __func__);
	HALT();
}

//handle DMA controller accesses
//va = virtual address of DMA controller register
//pa = physical address of DMA controller regiter
//sas = size of access
//srt = general purpose register number
//wnr = write/read indicator
//il = instruction length
//void dmaprot_handle_dmacontroller_access(arm8_32_regs_t *r, u32 va, u32 pa, u32 sas, u32 srt, u32 wnr, u32 il){
void dmaprot_handle_dmacontroller_access(info_intercept_data_abort_t *ida){
	volatile u32 *dmac_reg;

	if(ida->sas != 0x2){
		_XDPRINTFSMP_("%s: invalid sas=%u. Halting!\n", __func__, ida->sas);
		HALT();
	}

	//_XDPRINTFSMP_("dmaprot: va=0x%08x, pa=0x%08x, sas=%u, srt=%u, wnr=%u, il=%u\n",
	//		__func__,_va, pa, sas, srt, wnr, il);

	dmac_reg = (u32 *)ida->pa;
	if(ida->wnr){
		//write
		u32 value = (u32)guest_regread(ida->r, ida->srt);
		//_XDPRINTFSMP_("%s: s2pgtbl DATA ABORT: value=0x%08x\n", __func__, value);
		if( ((u32)dmac_reg & 0x000000FFUL) == 0x04)
			dmaprot_sanitizecb(value);

		*dmac_reg = value;
	}else{
		//read
		u32 value = (u32)*dmac_reg;
		//_XDPRINTFSMP_("%s: s2pgtbl DATA ABORT: value=0x%08x\n", __func__, value);
		guest_regwrite(ida->r, ida->srt, value);
	}

	//synchronize all memory accesses above
	cpu_dsb();
	cpu_isb();
}
