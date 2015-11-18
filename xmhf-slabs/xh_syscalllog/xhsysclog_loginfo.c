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


// logs given info into memory buffer sl_log
static void sl_loginfo(bool syscallmodified, u8 *digest, x86regs_t *r){
    if(sl_log_index < MAX_SL_LOG_SIZE){
        sl_log[sl_log_index].syscallmodified = syscallmodified;
        memcpy(&sl_log[sl_log_index].syscalldigest, digest, SHA_DIGEST_LENGTH);
        memcpy(&sl_log[sl_log_index].r, r, sizeof(x86regs_t));
        sl_log_index++;
    }
}



// memory fault
void sysclog_loginfo(u32 cpuindex, u32 guest_slab_index, u64 gpa, u64 gva, u64 errorcode){
    slab_params_t spl;
    xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
        (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;
    xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs =
        (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
    u8 syscalldigest[SHA_DIGEST_LENGTH];
    bool syscallhandler_modified=false;
    x86regs_t r;

    if(!_sl_registered)
        return;


_XDPRINTF_("%s[%u]: memory fault in guest slab %u; gpa=%016llx, gva=%016llx, errorcode=%016llx, sysenter execution?\n",
    __func__, (u16)cpuindex, guest_slab_index, gpa, gva, errorcode);


    spl.src_slabid = XMHFGEEC_SLAB_XH_SYSCALLLOG;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;


    //read GPR state
     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
    XMHF_SLAB_CALLNEW(&spl);
    memcpy(&r, &gcpustate_gprs->gprs, sizeof(x86regs_t));

    //copy code page at SYSENTER (referenced by shadow_sysenter_rip)
    CASM_FUNCCALL(xmhfhw_sysmemaccess_copy, &_sl_pagebuffer,
		shadow_sysenter_rip, sizeof(_sl_pagebuffer));

    //compute SHA-1 of the syscall page
    sha1(&_sl_pagebuffer, sizeof(_sl_pagebuffer), syscalldigest);

    //check to see if syscall handler has been modified
    if(memcmp(&_sl_syscalldigest, &syscalldigest, SHA_DIGEST_LENGTH))
        syscallhandler_modified=true;

	_XDPRINTF_("%s[%u]: syscall modified = %s\n",
	    __func__, (u16)cpuindex, (syscallhandler_modified ? "true" : "false"));


    //log GPR state, syscall modified status and digest
    sl_loginfo(syscallhandler_modified, &syscalldigest, &r);

    //set guest RIP to shadow_sysenter_rip to continue execution
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
    gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
    gcpustate_vmrwp->value = shadow_sysenter_rip;
    XMHF_SLAB_CALLNEW(&spl);

}

