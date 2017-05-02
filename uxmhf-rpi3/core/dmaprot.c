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
	volatile dmac_cb_t *dmacb_new;
	volatile dmac_cb_t *dmacb_start;

	//u32 i=0;

	dmacb = dmacb_start = (dmac_cb_t *)cb_syspa;

	//for(i=0; i < 64; i++){
	while(1){
		//i++;
		//if(i > 128)
		//	_XDPRINTFSMP_("dmaprot(%u): 0x%08x\n",i , dmacb);

		if( 	((dmapa_to_syspa(dmacb->src_addr) >= UXMHF_CORE_START_ADDR) &&
				(dmapa_to_syspa(dmacb->src_addr) < UXMHF_CORE_END_ADDR)) ||
				((dmapa_to_syspa(dmacb->dst_addr) >= UXMHF_CORE_START_ADDR) &&
				(dmapa_to_syspa(dmacb->dst_addr) < UXMHF_CORE_END_ADDR))
		){
				_XDPRINTFSMP_("%s: CB using I/O or micro-hypervisor memory regions. Halting!\n",
						__func__);
				HALT();
		}


		dmacb_new = (dmac_cb_t *)dmapa_to_syspa(dmacb->next_cb_addr);

		if(dmacb_new == 0)
			break;

		if(dmacb_new == dmacb_start)
			break;

		if(dmacb_new < dmacb)
			dmacb_start = dmacb_new;

		dmacb = dmacb_new;
	}

	//if(i==64){
	//	_XDPRINTFSMP_("%s: CB linked-list too large. Halting!\n",
	//			__func__);
	//	HALT();
	//}ss

/*	if( ((u32)dmacb >= BCM2837_PERIPHERALS_BASE) ||
		(
				((dmapa_to_syspa(dmacb->src_addr) >= UXMHF_CORE_START_ADDR) &&
				(dmapa_to_syspa(dmacb->src_addr) < UXMHF_CORE_END_ADDR)) ||
				((dmapa_to_syspa(dmacb->dst_addr) >= UXMHF_CORE_START_ADDR) &&
				(dmapa_to_syspa(dmacb->dst_addr) < UXMHF_CORE_END_ADDR))
		)
	  ){
		_XDPRINTFSMP_("%s: CB using I/O or micro-hypervisor memory regions. Halting!\n",
				__func__);
		HALT();
	}
*/

/*	if( 	((dmapa_to_syspa(dmacb->src_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->src_addr) < UXMHF_CORE_END_ADDR)) ||
			((dmapa_to_syspa(dmacb->dst_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->dst_addr) < UXMHF_CORE_END_ADDR))
	){
			_XDPRINTFSMP_("%s: CB using I/O or micro-hypervisor memory regions. Halting!\n",
					__func__);
			HALT();
	}


	dmacb = (dmac_cb_t *)dmapa_to_syspa(dmacb->next_cb_addr);
	if(dmacb == 0)
		goto end_dmaprot_sanitizecb;

	if( 	((dmapa_to_syspa(dmacb->src_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->src_addr) < UXMHF_CORE_END_ADDR)) ||
			((dmapa_to_syspa(dmacb->dst_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->dst_addr) < UXMHF_CORE_END_ADDR))
	){
			_XDPRINTFSMP_("%s: CB using I/O or micro-hypervisor memory regions. Halting!\n",
					__func__);
			HALT();
	}

	dmacb = (dmac_cb_t *)dmapa_to_syspa(dmacb->next_cb_addr);
	if(dmacb == 0)
		goto end_dmaprot_sanitizecb;

	if( 	((dmapa_to_syspa(dmacb->src_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->src_addr) < UXMHF_CORE_END_ADDR)) ||
			((dmapa_to_syspa(dmacb->dst_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->dst_addr) < UXMHF_CORE_END_ADDR))
	){
			_XDPRINTFSMP_("%s: CB using I/O or micro-hypervisor memory regions. Halting!\n",
					__func__);
			HALT();
	}

	dmacb = (dmac_cb_t *)dmapa_to_syspa(dmacb->next_cb_addr);
	if(dmacb == 0)
		goto end_dmaprot_sanitizecb;

	if( 	((dmapa_to_syspa(dmacb->src_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->src_addr) < UXMHF_CORE_END_ADDR)) ||
			((dmapa_to_syspa(dmacb->dst_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->dst_addr) < UXMHF_CORE_END_ADDR))
	){
			_XDPRINTFSMP_("%s: CB using I/O or micro-hypervisor memory regions. Halting!\n",
					__func__);
			HALT();
	}

	dmacb = (dmac_cb_t *)dmapa_to_syspa(dmacb->next_cb_addr);
	if(dmacb == 0)
		goto end_dmaprot_sanitizecb;

	if( 	((dmapa_to_syspa(dmacb->src_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->src_addr) < UXMHF_CORE_END_ADDR)) ||
			((dmapa_to_syspa(dmacb->dst_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->dst_addr) < UXMHF_CORE_END_ADDR))
	){
			_XDPRINTFSMP_("%s: CB using I/O or micro-hypervisor memory regions. Halting!\n",
					__func__);
			HALT();
	}

	dmacb = (dmac_cb_t *)dmapa_to_syspa(dmacb->next_cb_addr);
	if(dmacb == 0)
		goto end_dmaprot_sanitizecb;

	if( 	((dmapa_to_syspa(dmacb->src_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->src_addr) < UXMHF_CORE_END_ADDR)) ||
			((dmapa_to_syspa(dmacb->dst_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->dst_addr) < UXMHF_CORE_END_ADDR))
	){
			_XDPRINTFSMP_("%s: CB using I/O or micro-hypervisor memory regions. Halting!\n",
					__func__);
			HALT();
	}

	dmacb = (dmac_cb_t *)dmapa_to_syspa(dmacb->next_cb_addr);
	if(dmacb == 0)
		goto end_dmaprot_sanitizecb;

	if( 	((dmapa_to_syspa(dmacb->src_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->src_addr) < UXMHF_CORE_END_ADDR)) ||
			((dmapa_to_syspa(dmacb->dst_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->dst_addr) < UXMHF_CORE_END_ADDR))
	){
			_XDPRINTFSMP_("%s: CB using I/O or micro-hypervisor memory regions. Halting!\n",
					__func__);
			HALT();
	}

	dmacb = (dmac_cb_t *)dmapa_to_syspa(dmacb->next_cb_addr);
	if(dmacb == 0)
		goto end_dmaprot_sanitizecb;

	if( 	((dmapa_to_syspa(dmacb->src_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->src_addr) < UXMHF_CORE_END_ADDR)) ||
			((dmapa_to_syspa(dmacb->dst_addr) >= UXMHF_CORE_START_ADDR) &&
			(dmapa_to_syspa(dmacb->dst_addr) < UXMHF_CORE_END_ADDR))
	){
			_XDPRINTFSMP_("%s: CB using I/O or micro-hypervisor memory regions. Halting!\n",
					__func__);
			HALT();
	}


end_dmaprot_sanitizecb:
	return;
*/
}


void dmaprot_channel_cs_write(u32 *dmac_reg, u32 value){
	volatile u32 *dmac_cb_reg;
	u32 dmac_cb_reg_value;

	dmac_cb_reg = (u32 *)((u32)dmac_reg + 0x4);


	if(value & 0x1){
		//activating DMA
		dmac_cb_reg_value = *dmac_cb_reg;

		//_XDPRINTFSMP_("dmaprot: cs_write [ACTIVATE]\n");
		dmaprot_sanitizecb(dmac_cb_reg_value);
	}else{
		//deactivating DMA
		//_XDPRINTFSMP_("dmaprot: cs_write [DE-ACTIVATE]\n");
	}

	//synchronize all memory accesses above
	cpu_dsb();
	cpu_isb();


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
	u32 dmac_reg_page;
	u32 dmac_reg_off;
	u32 dmac_channel;

	//we only support 32-bit dmac accesses; bail out if this is not the case
	if(ida->sas != 0x2){
		_XDPRINTFSMP_("%s: invalid sas=%u. Halting!\n", __func__, ida->sas);
		HALT();
	}

	//compute dmac register address and register page-base
	dmac_reg = (u32 *)ida->pa;
	dmac_reg_page = (u32)dmac_reg & 0xFFFFF000UL;

	//compute channel and register offset
	if(dmac_reg_page == BCM2837_DMA15_REGS_BASE){
		dmac_channel = 15;
		dmac_reg_off = (u32)dmac_reg & 0x000000FFUL;
	}else{
		dmac_channel = (u32)dmac_reg & 0x00000F00UL;
		if(dmac_channel == 15) //this is either int status or enable base register
			dmac_channel = 16; //so set dmac_reg_channel to invalid value (16)
		dmac_reg_off = (u32)dmac_reg & 0x000000FFUL;
	}

	//act on either writes or reads
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


/*		if( ((u32)dmac_reg == (BCM2837_DMA0_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA1_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA2_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA3_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA4_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA5_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA6_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA7_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA8_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA9_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA10_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA11_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA12_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA13_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA14_REGS_BASE+0x4)) ||
					((u32)dmac_reg == (BCM2837_DMA15_REGS_BASE+0x4)) ){
				dmaprot_sanitizecb(value);

				//synchronize all memory accesses above
				cpu_dsb();
				cpu_isb();

				*dmac_reg = value;
*/
		}else{
			//synchronize all memory accesses above
			cpu_dsb();
			cpu_isb();

			*dmac_reg = value;
		}

	}else{
		//synchronize all memory accesses above
		cpu_dsb();
		cpu_isb();

		//read
		u32 value = (u32)*dmac_reg;
		//_XDPRINTFSMP_("%s: s2pgtbl DATA ABORT: value=0x%08x\n", __func__, value);
		guest_regwrite(ida->r, ida->srt, value);
	}

}

/*

		if( ((u32)dmac_reg == (BCM2837_DMA0_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA1_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA2_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA3_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA4_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA5_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA6_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA7_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA8_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA9_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA10_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA11_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA12_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA13_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA14_REGS_BASE + 0x1c)) ||
				((u32)dmac_reg == (BCM2837_DMA15_REGS_BASE + 0x1c)) ){
			_XDPRINTFSMP_("dmaprot: direct write to next cb addr reg. Halting\n");
			HALT();

*/
