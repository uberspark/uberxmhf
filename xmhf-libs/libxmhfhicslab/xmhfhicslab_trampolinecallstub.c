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
 * trampoline call stub
 * author: amit vasudevan (amitvasudevan@acm.org)
*/


#include <xmhf.h>
//#include <xmhfhicslab.h>
#include <xmhf-hic.h>
#include <xmhf-debug.h>

void __slab_calltrampolinenew(slab_params_t *sp){
    u32 errorcode;

    switch (_xmhfhic_common_slab_info_table[sp->dst_slabid].archdata.slabtype){

        case HIC_SLAB_X86VMXX86PC_HYPERVISOR:{
            FPSLABMAIN slab_main;

            slab_main = (FPSLABMAIN)_xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub;
            //_XDPRINTF_("%s: slab_main at %08x\n", __func__, (u32)slab_main);
            slab_main(sp);
        }
        break;

        case HIC_SLAB_X86VMXX86PC_GUEST:{
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VPID, sp->dst_slabid );
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_FULL, _xmhfhic_common_slab_info_table[sp->dst_slabid].archdata.mempgtbl_cr3);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_HIGH, 0);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RSP, _xmhfhic_common_slab_info_table[sp->dst_slabid].archdata.slabtos[(u16)sp->cpuid]);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RIP, _xmhfhic_common_slab_info_table[sp->dst_slabid].entrystub);

            errorcode = CASM_FUNCCALL(__slab_calltrampolinenew_h2g, NULL);

            switch(errorcode){
                case 0:	//no error code, VMCS pointer is invalid
                    _XDPRINTF_("%s: VMLAUNCH error; VMCS pointer invalid?\n", __func__);
                    break;
                case 1:{//error code available, so dump it
                    u32 code=xmhfhw_cpu_x86vmx_vmread(VMCS_INFO_VMINSTR_ERROR);
                    _XDPRINTF_("\n%s: VMLAUNCH error; code=%x\n", __func__, code);
                    break;
                }
            }

            HALT();

        }
        break;

        default:
        break;
    }

}
