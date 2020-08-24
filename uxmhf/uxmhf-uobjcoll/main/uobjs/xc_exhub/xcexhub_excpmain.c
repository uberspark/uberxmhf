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


/*
 * uXMHF core exception handling uobj
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <xmhfgeec.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_exhub.h>


static void _xcexhub_unhandled(x86vmx_exception_frame_t *exframe){
    //dump relevant info
    _XDPRINTF_("exception %x\n", exframe->vector);
    _XDPRINTF_("state dump:\n\n");
    _XDPRINTF_("errorcode=0x%08x\n", exframe->error_code);
    _XDPRINTF_("CS:EIP:EFLAGS = 0x%08x:0x%08x:0x%08x\n", exframe->orig_cs, exframe->orig_rip, exframe->orig_rflags);
    _XDPRINTF_("SS:ESP = 0x%08x:0x%08x\n", exframe->orig_ss, exframe->orig_rsp);
    _XDPRINTF_("CR0=0x%08x, CR2=0x%08x\n", CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr0,CASM_NOPARAM), CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr2,CASM_NOPARAM));
    _XDPRINTF_("CR3=0x%08x, CR4=0x%08x\n", CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr3,CASM_NOPARAM), CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr4,CASM_NOPARAM));
    _XDPRINTF_("CS=0x%04x, DS=0x%04x, ES=0x%04x, SS=0x%04x\n",
               (uint16_t)read_segreg_cs(CASM_NOPARAM), (uint16_t)read_segreg_ds(CASM_NOPARAM),
               (uint16_t)read_segreg_es(CASM_NOPARAM), (uint16_t)read_segreg_ss(CASM_NOPARAM));
    _XDPRINTF_("FS=0x%04x, GS=0x%04x\n", (uint16_t)read_segreg_fs(CASM_NOPARAM), (uint16_t)read_segreg_gs(CASM_NOPARAM));
    _XDPRINTF_("TR=0x%04x\n", (uint16_t)read_tr_sel(CASM_NOPARAM));
    _XDPRINTF_("EAX=0x%08x, EBX=0x%08x\n", exframe->eax, exframe->ebx);
    _XDPRINTF_("ECX=0x%08x, EDX=0x%08x\n", exframe->ecx, exframe->edx);
    _XDPRINTF_("ESI=0x%08x, EDI=0x%08x\n", exframe->esi, exframe->edi);
    _XDPRINTF_("EBP=0x%08x, ESP=0x%08x\n", exframe->ebp, exframe->esp);

    ////do a stack dump in the hopes of getting more info.
    //{
    //    uint64_t i;
    //    uint64_t stack_start = exframe->orig_rsp;
    //    _XDPRINTF_("\n-----stack dump (8 entries)-----\n");
    //    for(i=stack_start; i < stack_start+(8*sizeof(uint64_t)); i+=sizeof(uint64_t)){
    //        _XDPRINTF_("Stack(0x%016llx) -> 0x%016llx\n", i, *(uint64_t *)i);
    //    }
    //    _XDPRINTF_("\n-----stack dump end-------------\n");
    //}

}




#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
uint32_t check_esp, check_eip = CASM_RET_EIP;
slab_params_t test_sp;
uint32_t cpuid = 0;	//cpu id

void main(void){
	//populate hardware model stack and program counter
	hwm_cpu_gprs_esp = _slab_tos[cpuid];
	hwm_cpu_gprs_eip = check_eip;
	check_esp = hwm_cpu_gprs_esp; // pointing to top-of-stack

    test_sp.slab_ctype = framac_nondetu32();
    test_sp.src_slabid = framac_nondetu32();
    test_sp.dst_slabid = framac_nondetu32();
    test_sp.dst_uapifn = framac_nondetu32();
    test_sp.cpuid = framac_nondetu32();
	test_sp.in_out_params[0] =  framac_nondetu32(); 	test_sp.in_out_params[1] = framac_nondetu32();
	test_sp.in_out_params[2] = framac_nondetu32(); 	test_sp.in_out_params[3] = framac_nondetu32();
	test_sp.in_out_params[4] = framac_nondetu32(); 	test_sp.in_out_params[5] = framac_nondetu32();
	test_sp.in_out_params[6] = framac_nondetu32(); 	test_sp.in_out_params[7] = framac_nondetu32();
	test_sp.in_out_params[8] = framac_nondetu32(); 	test_sp.in_out_params[9] = framac_nondetu32();
	test_sp.in_out_params[10] = framac_nondetu32(); 	test_sp.in_out_params[11] = framac_nondetu32();
	test_sp.in_out_params[12] = framac_nondetu32(); 	test_sp.in_out_params[13] = framac_nondetu32();
	test_sp.in_out_params[14] = framac_nondetu32(); 	test_sp.in_out_params[15] = framac_nondetu32();

	xcexhub_excpmain(&test_sp);

	/*@assert ((hwm_cpu_state == CPU_STATE_RUNNING && hwm_cpu_gprs_esp == check_esp && hwm_cpu_gprs_eip == check_eip) ||
		(hwm_cpu_state == CPU_STATE_HALT));
	@*/
}
#endif

void xcexhub_excpmain(slab_params_t *sp){
	x86vmx_exception_frame_t *exframe = (x86vmx_exception_frame_t *)&sp->in_out_params[0];

	_XDPRINTF_("XC_EXHUB[%u]: Got control: ESP=%08x, src_slabid=%u, dst_slabid=%u\n",
				(uint16_t)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM), sp->src_slabid, sp->dst_slabid);

	if(exframe->vector == 0x3){
		_xcexhub_unhandled(exframe);
		_XDPRINTF_("%s: exception 3, returning\n", __func__);
	}else{
		_xcexhub_unhandled(exframe);
		_XDPRINTF_("\nHalting System!\n");
		CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__hlt, CASM_NOPARAM);
	}

	return;
}


