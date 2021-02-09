/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*
	Pi3 DMA protection implementation

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/debug.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/dmaprot.h>
//#include <uberspark/include/uberspark.h>

__attribute__((section(".palign2mdata"))) __attribute__((align(PAGE_SIZE_2M))) dmac_cb_t dmac_cblist[BCM2837_DMA_NUMCHANNELS][BCM2837_DMA_MAXCBRECORDS];

//activate DMA protection mechanism
void dmaprot_activate(void){
	u64 attrs_dev = (LDESC_S2_MC_DEVnGnRE << LDESC_S2_MEMATTR_MC_SHIFT) |
			(LDESC_S2_S2AP_NO_ACCESS << LDESC_S2_MEMATTR_S2AP_SHIFT) |
			(MEM_NON_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
			LDESC_S2_MEMATTR_AF_MASK;

	u64 attrs_dev_dwc = (LDESC_S2_MC_DEVnGnRE << LDESC_S2_MEMATTR_MC_SHIFT) |
			(LDESC_S2_S2AP_READ_ONLY << LDESC_S2_MEMATTR_S2AP_SHIFT) |
			(MEM_NON_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
			LDESC_S2_MEMATTR_AF_MASK;


	uapi_s2pgtbl_setprot(BCM2837_DMA0_REGS_BASE, attrs_dev);
	sysreg_tlbiallis();
	uapi_s2pgtbl_setprot(BCM2837_DMA15_REGS_BASE, attrs_dev);
	sysreg_tlbiallis();

	//USB DMA controller
	uapi_s2pgtbl_setprot(DWC_REGS_BASE, attrs_dev_dwc);
	sysreg_tlbiallis();



}


u32 dmaprot_shadowcb(u32 dmac_channel, u32 cb_pa){
	u32 cb_syspa = dmapa_to_syspa(cb_pa);
	volatile dmac_cb_t *dmacb;
	volatile dmac_cb_t *dmacb_prev=0;
	u32 i=0;
	u32 syspa_src_addr;
	u32 syspa_dst_addr;

	dmacb = (dmac_cb_t *)cb_syspa;

	//uart_puts("dmaprot: ccb: dmacb=");
	//debug_hexdumpu32((u32)dmacb);

	while(1){

		//uart_puts("dmaprot: ccb: ti=");
		//debug_hexdumpu32(dmacb->ti);
		//uart_puts("dmaprot: ccb: src_addr=");
		//debug_hexdumpu32(dmacb->src_addr);
		//uart_puts("dmaprot: ccb: dst_addr=");
		//debug_hexdumpu32(dmacb->dst_addr);
		//uart_puts("dmaprot: ccb: len=");
		//debug_hexdumpu32(dmacb->len);
		//uart_puts("dmaprot: ccb: next_cb_addr=");
		//debug_hexdumpu32(dmacb->next_cb_addr);

		syspa_src_addr = dmapa_to_syspa(dmacb->src_addr);
		syspa_dst_addr = dmapa_to_syspa(dmacb->dst_addr);

		if( 	(syspa_src_addr >= __UBERSPARK_UOBJCOLL_CONFIGDEF_UXMHF_CORE_START_ADDR__ &&
				 syspa_src_addr < __UBERSPARK_UOBJCOLL_CONFIGDEF_UXMHF_CORE_END_ADDR__)
		){
			uart_puts("CB src_addr using micro-hypervisor memory regions. Halting!\n");
			HALT();
		}

		if( 	(syspa_dst_addr >= __UBERSPARK_UOBJCOLL_CONFIGDEF_UXMHF_CORE_START_ADDR__ &&
				 syspa_dst_addr < __UBERSPARK_UOBJCOLL_CONFIGDEF_UXMHF_CORE_END_ADDR__)
		){
			uart_puts("CB dst_addr using micro-hypervisor memory regions. Halting!\n");
			HALT();
		}

		dmac_cblist[dmac_channel][i].ti = dmacb->ti;
		dmac_cblist[dmac_channel][i].src_addr = dmacb->src_addr;
		dmac_cblist[dmac_channel][i].dst_addr = dmacb->dst_addr;
		dmac_cblist[dmac_channel][i].len = dmacb->len;
		dmac_cblist[dmac_channel][i].stride = dmacb->stride;
		dmac_cblist[dmac_channel][i].rsv_0 = dmacb->rsv_0;
		dmac_cblist[dmac_channel][i].rsv_1 = dmacb->rsv_1;



		if(dmacb->next_cb_addr == 0){
			dmac_cblist[dmac_channel][i].next_cb_addr = 0;
			i++;
			break;
		}

		if(dmacb->next_cb_addr == cb_pa){
			dmac_cblist[dmac_channel][i].next_cb_addr = syspa_to_dmapa((u32)&dmac_cblist[dmac_channel][0].ti);
			i++;
			break;
		}

		if(dmapa_to_syspa(dmacb->next_cb_addr) == dmacb_prev){
			dmac_cblist[dmac_channel][i].next_cb_addr = syspa_to_dmapa((u32)&dmac_cblist[dmac_channel][i-1].ti);
			i++;
			break;
		}

		dmacb_prev = dmacb;
		dmacb = (dmac_cb_t *)dmapa_to_syspa(dmacb->next_cb_addr);

		if((i+1) >= BCM2837_DMA_MAXCBRECORDS){
			uart_puts("dmaprot: ccb: i < max records. Halting!\n");
			HALT();
		}
		dmac_cblist[dmac_channel][i].next_cb_addr = syspa_to_dmapa((u32)&dmac_cblist[dmac_channel][i+1].ti);
		i++;
	}

	//debug
	/*uart_puts("dumping shadow cb:\n");
	{
		u32 count;
		for(count=0; count < i; count++){
			uart_puts("ti = ");
			debug_hexdumpu32(dmac_cblist[dmac_channel][count].ti);
			uart_puts("src_addr = ");
			debug_hexdumpu32(dmac_cblist[dmac_channel][count].src_addr);
			uart_puts("dst_addr = ");
			debug_hexdumpu32(dmac_cblist[dmac_channel][count].dst_addr);
			uart_puts("len = ");
			debug_hexdumpu32(dmac_cblist[dmac_channel][count].len);
			uart_puts("next_cb_addr = ");
			debug_hexdumpu32(dmac_cblist[dmac_channel][count].next_cb_addr);
		}
	}
	uart_puts("dumping done; retval=\n");
	debug_hexdumpu32(syspa_to_dmapa((u32)&dmac_cblist[dmac_channel][0].ti));
	*/

	return syspa_to_dmapa((u32)&dmac_cblist[dmac_channel][0].ti);
}

/*
void dmaprot_dump_cb(u32 cb_pa){
	u32 cb_syspa = dmapa_to_syspa(cb_pa);
	volatile dmac_cb_t *dmacb;

	dmacb = (dmac_cb_t *)cb_syspa;

	uart_puts("dmaprot_dump_cb=");
	debug_hexdumpu32(cb_pa);
	uart_puts("  ti=");
	debug_hexdumpu32(dmacb->ti);
	uart_puts("  src_addr=");
	debug_hexdumpu32(dmacb->src_addr);
	uart_puts("  dst_addr=");
	debug_hexdumpu32(dmacb->dst_addr);
	uart_puts("  len=");
	debug_hexdumpu32(dmacb->len);
	uart_puts("  next_cb_addr=");
	debug_hexdumpu32(dmacb->next_cb_addr);
	uart_puts("dmaprot_dump_end\n");

}
*/

/*
void dmaprot_channel_cs_access(u32 wnr, u32 dmac_channel, u32 *dmac_reg, u32 value){
	volatile u32 *dmac_cb_reg;

	u32 dmac_cb_reg_value;

	dmac_cb_reg = (u32 *)((u32)dmac_reg + 0x4);

	if(wnr){	//write
		if(value & 0x1){
			//activating DMA, get current cb register value
			dmac_cb_reg_value = *dmac_cb_reg;

			uart_puts("dmaprot: DMA_ACTIVATE=");
			debug_hexdumpu32(dmac_cb_reg_value);
		}else{
			uart_puts("dmaprot: DMA_DE-ACTIVATE\n");
		}

		cpu_dsb();
		cpu_isb();	//synchronize all memory accesses above
		*dmac_reg = value;

	}else{		//read
		_XDPRINTFSMP_("%s: not implemented. Halting!\n",__func__);
		HALT();
	}

}
*/

void dmaprot_channel_conblkad_access(u32 wnr, u32 dmac_channel, u32 *dmac_reg, u32 value){
	u32 shadow_value;

	if(wnr){	//write
		//shadow cb
		//uart_puts("dmaprot: conblkad=");
		//debug_hexdumpu32(value);
		shadow_value=dmaprot_shadowcb(dmac_channel, value);
		//uart_puts("dmaprot: conblkad[shadow]=");
		//debug_hexdumpu32(shadow_value);

		cpu_dsb();
		cpu_isb();	//synchronize all memory accesses above
		*dmac_reg = shadow_value;

	}else{		//read
		_XDPRINTFSMP_("%s: not implemented. Halting!\n",__func__);
		HALT();
	}

}


//handle DMA controller accesses
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
		dmac_channel = ((u32)dmac_reg & 0x00000F00UL) >> 8;
		if(dmac_channel == 15) //this is either int status or enable base register
			dmac_channel = 16; //so set dmac_reg_channel to invalid value (16)
		dmac_reg_off = (u32)dmac_reg & 0x000000FFUL;
	}

	//act on either writes or reads
	if(ida->wnr){	//dmac register write

		//compute value that is going to be written
		u32 value = (u32)guest_regread(ida->r, ida->srt);

		switch(dmac_reg_off){
			//case 0x0:	//CS register
				//dmaprot_channel_cs_access(ida->wnr, dmac_channel, dmac_reg, value);
				//break;

			case 0x4:	//CONBLKAD register
				dmaprot_channel_conblkad_access(ida->wnr, dmac_channel, dmac_reg, value);
				break;


			default:	//just pass-through writes
				cpu_dsb();
				cpu_isb();	//synchronize all memory accesses above
				*dmac_reg = value;
				break;
		}

	}else{	//dmac register read

		switch(dmac_reg_off){
			default:{	//just pass-through reads
					u32 value;
					cpu_dsb();
					cpu_isb();	//synchronize all memory accesses above
					value = (u32)*dmac_reg;
					guest_regwrite(ida->r, ida->srt, value);
				}
				break;
		}

	}

}


//handle USB DMA controller accesses
void dmaprot_handle_usbdmac_access(info_intercept_data_abort_t *ida){
	u32 guest_regvalue;

	if(!ida->il){	//we only support 32-bit arm
		_XDPRINTFSMP_("dmaprotusb: il=0, unhandled condition. Halting!\n");
		HALT();
	}

	if(!ida->wnr){	//we only get here on writes, bail out otherwise
		_XDPRINTFSMP_("dmaprotusb: wnr=0, unhandled condition. Halting!\n");
		HALT();
	}

	//we only support 32-bit dmac accesses; bail out if this is not the case
	if(ida->sas != 0x2){
		_XDPRINTFSMP_("dmaprotusb: access is not 32-bits, unhandled condition. Halting!\n");
		HALT();
	}

	//get guest register value
	guest_regvalue = guest_regread(ida->r, ida->srt);

	mmio_write32(ida->pa, guest_regvalue);
}
