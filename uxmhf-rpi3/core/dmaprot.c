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

__attribute__((section(".palign2mdata"))) __attribute__((align(PAGE_SIZE_2M))) dmac_cb_t dmac_cblist[BCM2837_DMA_NUMCHANNELS][BCM2837_DMA_MAXCBRECORDS];

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



u32 dmaprot_checkcb(u32 dmac_channel, u32 cb_pa){
	u32 cb_syspa = dmapa_to_syspa(cb_pa);
	volatile dmac_cb_t *dmacb;
	volatile dmac_cb_t *dmacb_new;
	volatile dmac_cb_t *dmacb_start;
	u32 i=0;
	//u32 count;

	//_XDPRINTFSMP_("%s: dmac_channel=%u, cb_pa=0x%08x, cb_syspa=0x%08x\n",
	//		__func__, dmac_channel, cb_pa, cb_syspa);

	dmacb = dmacb_start = (dmac_cb_t *)cb_syspa;


	while(1){

		if( 	((dmapa_to_syspa(dmacb->src_addr) >= UXMHF_CORE_START_ADDR) &&
				(dmapa_to_syspa(dmacb->src_addr) < UXMHF_CORE_END_ADDR)) ||
				((dmapa_to_syspa(dmacb->dst_addr) >= UXMHF_CORE_START_ADDR) &&
				(dmapa_to_syspa(dmacb->dst_addr) < UXMHF_CORE_END_ADDR))
		){
				_XDPRINTFSMP_("%s: CB using I/O or micro-hypervisor memory regions. Halting!\n",
						__func__);
				HALT();
		}

		dmac_cblist[dmac_channel][i].ti = dmacb->ti;
		dmac_cblist[dmac_channel][i].src_addr = dmacb->src_addr;
		dmac_cblist[dmac_channel][i].dst_addr = dmacb->dst_addr;
		dmac_cblist[dmac_channel][i].len = dmacb->len;
		dmac_cblist[dmac_channel][i].stride = dmacb->stride;
		dmac_cblist[dmac_channel][i].next_cb_addr = 0;
		dmac_cblist[dmac_channel][i].rsv_0 = dmacb->rsv_0;
		dmac_cblist[dmac_channel][i].rsv_1 = dmacb->rsv_1;


		dmacb_new = (dmac_cb_t *)dmapa_to_syspa(dmacb->next_cb_addr);

		if(dmacb_new == 0)
			break;

		if(dmacb_new == dmacb_start){
			dmac_cblist[dmac_channel][i].next_cb_addr = syspa_to_dmapa((u32)&dmac_cblist[dmac_channel][0].ti);
			break;
		}

		if(dmacb_new < dmacb){
			dmacb = dmacb_start = dmacb_new;
			i=0;
		}else{
			dmacb = dmacb_new;
			if((i+1) >= 128){
				_XDPRINTFSMP_("%s: max cb length reached. Halting!\n",__func__);
				HALT();
			}
			dmac_cblist[dmac_channel][i].next_cb_addr = syspa_to_dmapa((u32)&dmac_cblist[dmac_channel][i+1]);
			i++;
		}
	}

	//debug
/*	i++;
	_XDPRINTFSMP_("%s: dumping revised cb (len=%u)\n", __func__, i);
	for(count=0; count < i; count++){
		_XDPRINTFSMP_("[%u] ti = 0x%08x\n", count,
				dmac_cblist[dmac_channel][count].ti);
		_XDPRINTFSMP_("[%u] src_addr = 0x%08x\n", count,
				dmac_cblist[dmac_channel][count].src_addr);
		_XDPRINTFSMP_("[%u] dst_addr = 0x%08x\n", count,
				dmac_cblist[dmac_channel][count].dst_addr);
		_XDPRINTFSMP_("[%u] len = 0x%08x\n", count,
				dmac_cblist[dmac_channel][count].len);
		_XDPRINTFSMP_("[%u] stride = 0x%08x\n", count,
				dmac_cblist[dmac_channel][count].stride);
		_XDPRINTFSMP_("[%u] next_cb_addr = 0x%08x\n", count,
				dmac_cblist[dmac_channel][count].next_cb_addr);
	}

	_XDPRINTFSMP_("%s: returning 0x%08x. Halting\n", __func__, syspa_to_dmapa((u32)&dmac_cblist[dmac_channel][0]));
	HALT();
*/
	return syspa_to_dmapa((u32)&dmac_cblist[dmac_channel][0]);
}



u32 dmaprot_checkcblite(u32 dmac_channel, u32 cb_pa){
	u32 cb_syspa = dmapa_to_syspa(cb_pa);
	volatile dmac_cb_t *dmacb;
	volatile dmac_cb_t *dmacb_prev=0;
	u32 i=0;

	dmacb = (dmac_cb_t *)cb_syspa;

	//bcm2837_miniuart_puts("dmaprot: ccb: cb_pa=");
	//debug_hexdumpu32(cb_pa);

	while(1){

		//bcm2837_miniuart_puts("dmaprot: ccb: ti=");
		//debug_hexdumpu32(dmacb->ti);
		//bcm2837_miniuart_puts("dmaprot: ccb: src_addr=");
		//debug_hexdumpu32(dmacb->src_addr);
		//bcm2837_miniuart_puts("dmaprot: ccb: dst_addr=");
		//debug_hexdumpu32(dmacb->dst_addr);
		//bcm2837_miniuart_puts("dmaprot: ccb: len=");
		//debug_hexdumpu32(dmacb->len);
		//bcm2837_miniuart_puts("dmaprot: ccb: next_cb_addr=");
		//debug_hexdumpu32(dmacb->next_cb_addr);

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
			bcm2837_miniuart_puts("dmaprot: ccb: i < max records. Halting!\n");
			HALT();
		}
		dmac_cblist[dmac_channel][i].next_cb_addr = syspa_to_dmapa((u32)&dmac_cblist[dmac_channel][i+1].ti);
		i++;
	}

	//debug
	/*bcm2837_miniuart_puts("dumping shadow cb:\n");
	{
		u32 count;
		for(count=0; count < i; count++){
			bcm2837_miniuart_puts("ti = ");
			debug_hexdumpu32(dmac_cblist[dmac_channel][count].ti);
			bcm2837_miniuart_puts("src_addr = ");
			debug_hexdumpu32(dmac_cblist[dmac_channel][count].src_addr);
			bcm2837_miniuart_puts("dst_addr = ");
			debug_hexdumpu32(dmac_cblist[dmac_channel][count].dst_addr);
			bcm2837_miniuart_puts("len = ");
			debug_hexdumpu32(dmac_cblist[dmac_channel][count].len);
			bcm2837_miniuart_puts("next_cb_addr = ");
			debug_hexdumpu32(dmac_cblist[dmac_channel][count].next_cb_addr);
		}
	}
	bcm2837_miniuart_puts("dumping done; retval=\n");
	debug_hexdumpu32((u32)&dmac_cblist[dmac_channel][0].ti);
	*/

	return syspa_to_dmapa((u32)&dmac_cblist[dmac_channel][0].ti);
}


void dmaprot_dump_cb(u32 cb_pa){
	u32 cb_syspa = dmapa_to_syspa(cb_pa);
	volatile dmac_cb_t *dmacb;

	dmacb = (dmac_cb_t *)cb_syspa;

	bcm2837_miniuart_puts("dmaprot_dump_cb=");
	debug_hexdumpu32(cb_pa);
	bcm2837_miniuart_puts("  ti=");
	debug_hexdumpu32(dmacb->ti);
	bcm2837_miniuart_puts("  src_addr=");
	debug_hexdumpu32(dmacb->src_addr);
	bcm2837_miniuart_puts("  dst_addr=");
	debug_hexdumpu32(dmacb->dst_addr);
	bcm2837_miniuart_puts("  len=");
	debug_hexdumpu32(dmacb->len);
	bcm2837_miniuart_puts("  next_cb_addr=");
	debug_hexdumpu32(dmacb->next_cb_addr);
	bcm2837_miniuart_puts("dmaprot_dump_end\n");

}

//u32 once_cs=0;

void dmaprot_channel_cs_access(u32 wnr, u32 dmac_channel, u32 *dmac_reg, u32 value){
	volatile u32 *dmac_cb_reg;
	//volatile u32 *dmac_ti_reg;
	//volatile u32 *dmac_src_reg;

	u32 dmac_cb_reg_value;
	//u32 dmac_cs_reg_value;
	//u32 dmac_ti_reg_value;
	//u32 dmac_src_reg_value;

	dmac_cb_reg = (u32 *)((u32)dmac_reg + 0x4);
	//dmac_ti_reg = (u32 *)((u32)dmac_reg + 0x8);
	//dmac_src_reg = (u32 *)((u32)dmac_reg + 0xc);

	if(wnr){	//write
		if(value & 0x1){
			//activating DMA, get current cb register value
			dmac_cb_reg_value = *dmac_cb_reg;

			bcm2837_miniuart_puts("dmaprot: DMA_ACTIVATE=");
			debug_hexdumpu32(dmac_cb_reg_value);
		}else{
			bcm2837_miniuart_puts("dmaprot: DMA_DE-ACTIVATE\n");
		}

		/*//debug
		{
			volatile dmac_cb_t *dmacb = (dmac_cb_t *)0x3A900000;
			volatile dmac_cb_t *dmacb_ref = (dmac_cb_t *)dmapa_to_syspa(dmac_cb_reg_value);

			dmacb->ti = dmacb_ref->ti;
			dmacb->src_addr = dmacb_ref->src_addr;
			dmacb->dst_addr = dmacb_ref->dst_addr;
			dmacb->len = dmacb_ref->len;
			dmacb->stride = dmacb_ref->stride;
			dmacb->next_cb_addr = dmacb_ref->next_cb_addr;
			dmacb->rsv_0 = dmacb_ref->rsv_0;
			dmacb->rsv_1 = dmacb_ref->rsv_1;

			*dmac_cb_reg = syspa_to_dmapa((u32)dmacb);
			dmac_cb_reg_value = *dmac_cb_reg;
		}*/


		cpu_dsb();
		cpu_isb();	//synchronize all memory accesses above
		*dmac_reg = value;

		//if(once_cs == 0){
			//dmaprot_dump_cb(dmac_cb_reg_value);

			//dmac_ti_reg_value = *dmac_ti_reg;
			//bcm2837_miniuart_puts("dmaprot: TI val=");
			//debug_hexdumpu32(dmac_ti_reg_value);
			//dmac_src_reg_value = *dmac_src_reg;
			//bcm2837_miniuart_puts("dmaprot: SRC val=");
			//debug_hexdumpu32(dmac_src_reg_value);

			//bcm2837_miniuart_puts("dmaprot: waiting for DMA to complete...\n");
			//while(*dmac_cb_reg != 0){

			//}
			//dmac_cs_reg_value = *dmac_reg;
			//bcm2837_miniuart_puts("dmaprot: DMA completed=");
			//debug_hexdumpu32(dmac_cs_reg_value);

			//once_cs = 1;
			//HALT();
		//}

	}else{		//read
		_XDPRINTFSMP_("%s: not implemented. Halting!\n",__func__);
		HALT();
	}

}

//u32 once=0;

void dmaprot_channel_conblkad_access(u32 wnr, u32 dmac_channel, u32 *dmac_reg, u32 value){
	u32 revised_value;

	if(wnr){	//write
		//check cb
		//revised_value=dmaprot_checkcb(dmac_channel, value);
		//dmaprot_checkcb(dmac_channel, value);
		//sprintf(dmaprot_logbuf[dmaprot_logbuf_index++][0], "dmaprot: conblkad=0x%08x\n", value);
		//bcm2837_miniuart_puts("dmaprot: conblkad=");
		//debug_hexdumpu32(value);
		revised_value=dmaprot_checkcblite(dmac_channel, value);
		//bcm2837_miniuart_puts("dmaprot: conblkad[revised]=");
		//debug_hexdumpu32(revised_value);

		cpu_dsb();
		cpu_isb();	//synchronize all memory accesses above
		//if(once < 2){
			*dmac_reg = revised_value;
			//once++;
		//}else{
		//	*dmac_reg = value;
		//}

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

