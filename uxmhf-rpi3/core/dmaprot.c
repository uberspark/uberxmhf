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
	volatile dmac_cb_t *dmacb;
	//u32 i;

	//_XDPRINTFSMP_("%s: cb_pa=0x%08x, cb_syspa=0x%08x\n", __func__, cb_pa, cb_syspa);
	dmacb = (dmac_cb_t *)cb_syspa;
	//i=0;

	while(1) {
		if(dmacb == 0)
			break;
		//i++;
		//if( i > 8)
		//	break;
		//_XDPRINTFSMP_("%s: dumping dmacb at 0x%08x...\n", __func__, dmacb);
		//_XDPRINTFSMP_("%s: ti=0x%08x\n", __func__, dmacb->ti);
		//_XDPRINTFSMP_("%s: src_addr=0x%08x\n", __func__, dmapa_to_syspa(dmacb->src_addr));
		//_XDPRINTFSMP_("%s: dst_addr=0x%08x\n", __func__, dmapa_to_syspa(dmacb->dst_addr));
		//_XDPRINTFSMP_("%s: len=0x%08x\n", __func__, dmacb->len);
		//_XDPRINTFSMP_("%s: stride=0x%08x\n", __func__, dmacb->stride);
		//_XDPRINTFSMP_("%s: next_cb_addr=0x%08x\n", __func__, dmacb->next_cb_addr);

	//for(i=0; i < 16; i++){
		/*if( ((dmapa_to_syspa(dmacb->src_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->src_addr) < UXMHF_CORE_END_ADDR)) ||
			((dmapa_to_syspa(dmacb->dst_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->dst_addr) < UXMHF_CORE_END_ADDR)) ){
			_XDPRINTFSMP_("%s: CB using micro-hypervisor memory regions. Halting!\n",
					__func__);
			HALT();
		}*/
	//}


		dmacb = (dmac_cb_t *)dmapa_to_syspa(dmacb->next_cb_addr);
	}

}


void dmaprot_channel_cs_write(u32 *dmac_reg, u32 value){
	*dmac_reg = value;
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
		if( ((u32)dmac_reg == (BCM2837_DMA0_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA1_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA2_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA3_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA4_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA5_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA6_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA7_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA8_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA9_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA10_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA11_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA12_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA13_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA14_REGS_BASE)) ||
				((u32)dmac_reg == (BCM2837_DMA15_REGS_BASE)) ){
			//dmaprot_sanitizecb(value);
			dmaprot_channel_cs_write(dmac_reg, value);
		}else{
			*dmac_reg = value;
		}

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
