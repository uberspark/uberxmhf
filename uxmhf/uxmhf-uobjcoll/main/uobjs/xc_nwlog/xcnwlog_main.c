/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_nwlog.h>

/*
 * xcnwlog_main: main uobj code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


//////
// entry function
//////


#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-hwm.h>

uint32_t cpuid = 0;	//BSP cpu
uint32_t check_esp, check_eip = CASM_RET_EIP;
slab_params_t test_sp;
typedef enum {
	XCNWLOG_VERIF_INIT,
	XCNWLOG_VERIF_LOGDATA
} xcnwlog_verif_t;

xcnwlog_verif_t xcnwlog_verif = XCNWLOG_VERIF_INIT;
bool xcnwlog_logdata_startedxmit = false;

void cbhwm_e1000_write_tdt(uint32_t origval, uint32_t newval){
	switch(xcnwlog_verif){
		case XCNWLOG_VERIF_INIT:
			//@assert 1;
			break;

		case XCNWLOG_VERIF_LOGDATA:{
			if(hwm_e1000_tctl & E1000_TCTL_EN){
				//@assert newval == 1;
				//@assert hwm_e1000_tdbah == 0;
				//@assert hwm_e1000_tdbal == (uint32_t)&xcnwlog_desc;
				//@assert hwm_e1000_status_transmitting == false;
				xcnwlog_logdata_startedxmit = true;
			}
			break;
		}

		default:
			//@assert 0;
			break;
	}
}

void cbhwm_e1000_write_tdbah(uint32_t origval, uint32_t newval){
	switch(xcnwlog_verif){
		case XCNWLOG_VERIF_INIT:
			//@assert 1;
			break;

		case XCNWLOG_VERIF_LOGDATA:{
			//@assert 0;
			break;
		}

		default:
			//@assert 0;
			break;
	}
}

void cbhwm_e1000_write_tdbal(uint32_t origval, uint32_t newval){
	switch(xcnwlog_verif){
		case XCNWLOG_VERIF_INIT:
			//@assert 1;
			break;

		case XCNWLOG_VERIF_LOGDATA:{
			//@assert 0;
			break;
		}

		default:
			//@assert 0;
			break;
	}
}

void cbhwm_e1000_write_tdlen(uint32_t origval, uint32_t newval){
	switch(xcnwlog_verif){
		case XCNWLOG_VERIF_INIT:
			//@assert 1;
			break;

		case XCNWLOG_VERIF_LOGDATA:{
			//@assert 0;
			break;
		}

		default:
			//@assert 0;
			break;
	}
}

void main(void){
	//populate hardware model stack and program counter
	hwm_cpu_gprs_esp = _slab_tos[cpuid];
	hwm_cpu_gprs_eip = check_eip;
	check_esp = hwm_cpu_gprs_esp; // pointing to top-of-stack

	test_sp.src_slabid = framac_nondetu32interval(0, XMHFGEEC_TOTAL_SLABS-1);
	test_sp.in_out_params[0] =  framac_nondetu32(); 	test_sp.in_out_params[1] = framac_nondetu32();
	test_sp.in_out_params[2] = framac_nondetu32(); 	test_sp.in_out_params[3] = framac_nondetu32();
	test_sp.in_out_params[4] = framac_nondetu32(); 	test_sp.in_out_params[5] = framac_nondetu32();
	test_sp.in_out_params[6] = framac_nondetu32(); 	test_sp.in_out_params[7] = framac_nondetu32();
	test_sp.in_out_params[8] = framac_nondetu32(); 	test_sp.in_out_params[9] = framac_nondetu32();
	test_sp.in_out_params[10] = framac_nondetu32(); 	test_sp.in_out_params[11] = framac_nondetu32();
	test_sp.in_out_params[12] = framac_nondetu32(); 	test_sp.in_out_params[13] = framac_nondetu32();
	test_sp.in_out_params[14] = framac_nondetu32(); 	test_sp.in_out_params[15] = framac_nondetu32();

	//execute harness
	xcnwlog_verif = XCNWLOG_VERIF_INIT;
	e1000_init_module();
	//@assert (e1000_adapt.hw.hw_addr == (uint8_t *)E1000_HWADDR_BASE);
	//@assert (e1000_adapt.tx_ring.tdt == (uint16_t)(E1000_TDT));
	//@assert (e1000_adapt.tx_ring.tdh == (uint16_t)(E1000_TDH));
        //@assert hwm_e1000_tdbah == 0;
	//@assert hwm_e1000_tdbal == (uint32_t)&xcnwlog_desc;
	//@assert hwm_e1000_tdlen == 4096;

	//@assert hwm_e1000_status_transmitting == false;
	xcnwlog_verif = XCNWLOG_VERIF_LOGDATA;
	e1000_xmitack();
	//@assert hwm_e1000_status_transmitting == false;

	//@assert hwm_cpu_gprs_esp == check_esp;
	//@assert hwm_cpu_gprs_eip == check_eip;
}
#endif



//@ ghost bool xcnwlog_methodcall_init = false;
//@ ghost bool xcnwlog_methodcall_logdata = false;
//@ ghost bool xcnwlog_methodcall_invalid = false;
/*@
	requires \valid(sp);
	ensures ( sp->dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_INITIALIZE) ==> (xcnwlog_methodcall_init == true);
	ensures ( sp->dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_LOGDATA ) ==> (xcnwlog_methodcall_logdata == true);
	ensures !(
		( sp->dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_INITIALIZE) ||
		( sp->dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_LOGDATA )
	) ==> (xcnwlog_methodcall_invalid == true);
@*/
void xcnwlog_slab_main(slab_params_t *sp){

	_XDPRINTF_("XCNWLOG[%u]: Got control: src=%u, dst=%u, esp=%08x, eflags=%08x\n",
		(uint16_t)sp->cpuid, sp->src_slabid, sp->dst_slabid, CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_esp,CASM_NOPARAM),
			CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_eflags, CASM_NOPARAM));

	if(sp->dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_INITIALIZE){
		xcnwlog_init();
		//@ghost xcnwlog_methodcall_init = true;

	}else if (sp->dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_LOGDATA){
		xcnwlog_ls_element_t elem;
		elem.logbuf[0] = sp->in_out_params[0]; 		elem.logbuf[1] = sp->in_out_params[0];
		elem.logbuf[2] = sp->in_out_params[0]; 		elem.logbuf[3] = sp->in_out_params[0];
		elem.logbuf[4] = sp->in_out_params[0]; 		elem.logbuf[5] = sp->in_out_params[0];
		elem.logbuf[6] = sp->in_out_params[0]; 		elem.logbuf[7] = sp->in_out_params[0];
		elem.logbuf[8] = sp->in_out_params[0]; 		elem.logbuf[9] = sp->in_out_params[0];
		elem.logbuf[10] = sp->in_out_params[0]; 		elem.logbuf[11] = sp->in_out_params[0];
		elem.logbuf[12] = sp->in_out_params[0]; 		elem.logbuf[13] = sp->in_out_params[0];
		elem.logbuf[14] = sp->in_out_params[0]; 		elem.logbuf[15] = sp->in_out_params[0];
		xcnwlog_logdata(elem);
		//@ghost xcnwlog_methodcall_logdata = true;

        }else {
		_XDPRINTF_("XCNWLOG[%u]: Unknown sub-function %x. Halting!\n",
		    (uint16_t)sp->cpuid, sp->dst_uapifn);
		//@ghost xcnwlog_methodcall_invalid = true;


        }

}







