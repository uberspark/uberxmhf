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

// syscalllog hypapp main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <uapi_gcpustate.h>
//#include <uapi_slabmemacc.h>
#include <uapi_slabmempgtbl.h>

#include <xh_syscalllog.h>




//register a syscall handler code page (at gpa)
//void sysclog_register(u32 cpuindex, u32 guest_slab_index, u64 gpa){
void sysclog_register(u32 cpuindex, u32 guest_slab_index, u32 syscall_page_paddr, u32 syscall_shadowpage_vaddr, u32 syscall_shadowpage_paddr){

        slab_params_t spl;

        _XDPRINTF_("%s[%u]: gid=%u, syscall_page_paddr=0x%08x\n",
        			__func__, (u16)cpuindex, guest_slab_index, syscall_page_paddr);
        _XDPRINTF_("%s[%u]: syscall_shadowpage_vaddr=0x%08x, syscall_shadowpage_paddr=0x%08x\n",
        			__func__, (u16)cpuindex, syscall_shadowpage_vaddr, syscall_shadowpage_paddr);

        spl.src_slabid = XMHFGEEC_SLAB_XH_SYSCALLLOG;
        spl.cpuid = cpuindex;

/*
        CASM_FUNCCALL(xmhfhw_sysmemaccess_copy, &_sl_pagebuffer, gpa, sizeof(_sl_pagebuffer));

        _XDPRINTF_("%s[%u]: grabbed page contents at gpa=%016llx\n",
               __func__, (u16)cpuindex, gpa);

        //compute SHA-1 of the syscall page
        sha1(&_sl_pagebuffer, sizeof(_sl_pagebuffer), _sl_syscalldigest);


        _XDPRINTF_("%s[%u]: computed SHA-1: %*D\n",
               __func__, (u16)cpuindex, SHA_DIGEST_LENGTH, _sl_syscalldigest, " ");
*/

        _XDPRINTF_("%s[%u]: halting wip!\n", __func__, (u16)cpuindex);
        _XDPRINTF_("XMHF Tester Finished!\n");
        HALT();

        _sl_registered=true;
}


