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
 * dummy module to generate libxmhfslab.a
 * author: amit vasudevan (amitvasudevan@acm.org)
*/


#include <xmhf.h>
//#include <xmhfhicslab.h>
#include <xmhf-hic.h>
#include <xmhf-debug.h>

/*
__slab_calltrampoline register mappings:

RDI = call type (XMHF_HIC_SLABCALL)
RSI = iparams
RDX = iparams_size
RCX = oparams
R8 = oparams_size
R9 = dst_slabid
R10 = return RSP;
R11 = return_address

*/


__attribute__((naked)) bool __slab_calltrampoline(u64 reserved,
    slab_input_params_t *iparams, u64 iparams_size,
    slab_output_params_t *oparams, u64 oparams_size, u64 dst_slabid){

/*  //TODO: x86_64 --> x86

    asm volatile (
        "pushq %%rbx \r\n"
        "pushq %%r12 \r\n"
        "pushq %%r13 \r\n"
        "pushq %%r14 \r\n"
        "pushq %%r15 \r\n"

        "movq %0, %%rdi \r\n"
        "movq %%rsp, %%r10 \r\n"
        "movq $1f, %%r11 \r\n"\
        "sysenter \r\n" \
        \
        "1:\r\n" \
        "popq %%r15 \r\n"
        "popq %%r14 \r\n"
        "popq %%r13 \r\n"
        "popq %%r12 \r\n"
        "popq %%rbx \r\n"
        "retq \r\n" \
        :
        : "i" (XMHF_HIC_SLABCALL)
        :
    );
*/

}



static void __slab_calltrampolinenew_h2g(void){
                    u32 errorcode;

                    asm volatile (
                            "vmlaunch\r\n"

                            "jc __vmx_start_hvm_failinvalid\r\n"
                            "jnz	__vmx_start_hvm_undefinedimplementation	\r\n"
                            "movl $0x1, %%eax\r\n"		//VMLAUNCH error, XXX: need to read from VM instruction error field in VMCS
                            "movl %%eax, %0 \r\n"
                            "jmp __vmx_start_continue \r\n"
                            "__vmx_start_hvm_undefinedimplementation:\r\n"
                            "movl $0x2, %%eax\r\n"		//violation of VMLAUNCH specs., handle it anyways
                            "movl %%eax, %0 \r\n"
                            "jmp __vmx_start_continue \r\n"
                            "__vmx_start_hvm_failinvalid:\r\n"
                            "xorl %%eax, %%eax\r\n"		//return 0 as we have no error code available
                            "movl %%eax, %0 \r\n"
                            "__vmx_start_continue:\r\n"
                        : "=g"(errorcode)
                        :
                        : "eax", "cc"
                    );


                    switch(errorcode){
                        case 0:	//no error code, VMCS pointer is invalid
                            _XDPRINTF_("%s: VMLAUNCH error; VMCS pointer invalid?\n", __FUNCTION__);
                            break;
                        case 1:{//error code available, so dump it
                            u32 code=xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMINSTR_ERROR);
                            _XDPRINTF_("\n%s: VMLAUNCH error; code=%x\n", __FUNCTION__, code);
                            break;
                        }
                    }

                    HALT();
}


void __slab_calltrampolinenew(slab_params_t *sp){

    switch (_xmhfhic_common_slab_info_table[sp->dst_slabid].archdata.slabtype){

        case HIC_SLAB_X86VMXX86PC_HYPERVISOR:{
            FPSLABMAIN slab_main;

            slab_main = (FPSLABMAIN)_xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub;
            slab_main(sp);
        }
        break;

        case HIC_SLAB_X86VMXX86PC_GUEST:{
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VPID, sp->dst_slabid );
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_FULL, _xmhfhic_common_slab_info_table[sp->dst_slabid].archdata.mempgtbl_cr3);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_HIGH, 0);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RSP, _xmhfhic_common_slab_info_table[sp->dst_slabid].archdata.slabtos[(u16)sp->cpuid]);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RIP, _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub);

            __slab_calltrampolinenew_h2g();

        }
        break;

        default:
        break;
    }

}
