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

// syscalllog hypapp
// author: amit vasudevan (amitvasudevan@acm.org)

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/uapi_gcpustate.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/uapi_slabmempgtbl.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc_nwlog.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xh_syscalllog.h>

//@ghost bool sysclog_loginfo_nwlogged=false;
/*@

	behavior yes_log:
		assumes (sl_activated && (((uint32_t)gpa & 0xFFFFF000UL) == sl_syscall_page_paddr));
		ensures sysclog_loginfo_nwlogged == true;

	behavior no_log:
		assumes !(sl_activated && (((uint32_t)gpa & 0xFFFFF000UL) == sl_syscall_page_paddr));
		ensures sysclog_loginfo_nwlogged == false;

	complete behaviors;
	disjoint behaviors;
@*/
bool sysclog_loginfo(uint32_t cpuindex, uint32_t guest_slab_index, uint64_t gpa, uint64_t gva, uint64_t errorcode){
	slab_params_t spl;
	xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
		(xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;

	if(sl_activated && (((uint32_t)gpa & 0xFFFFF000UL) == sl_syscall_page_paddr)){

		_XDPRINTF_("%s[%u]: syscall trapping in guest slab %u; gpa=0x%08x, gva=0x%08x, errorcode=0x%08x\n",
		__func__, (uint16_t)cpuindex, guest_slab_index, (uint32_t)gpa, (uint32_t)gva, (uint32_t)errorcode);


		spl.src_slabid = XMHFGEEC_SLAB_XH_SYSCALLLOG;
		spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
		spl.cpuid = cpuindex;

		//read GPR state
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
		//@assert spl.dst_slabid == XMHFGEEC_SLAB_UAPI_GCPUSTATE && spl.dst_uapifn == XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
		ugcpust_slab_main(&spl);

		//log GPR state for syscall
		spl.dst_slabid = XMHFGEEC_SLAB_XC_NWLOG;
		spl.dst_uapifn = XMHFGEEC_SLAB_XC_NWLOG_LOGDATA;
		//@assert spl.dst_slabid == XMHFGEEC_SLAB_XC_NWLOG && spl.dst_uapifn == XMHFGEEC_SLAB_XC_NWLOG_LOGDATA;
		xcnwlog_slab_main(&spl);
		//@ghost sysclog_loginfo_nwlogged = true;

		//set guest RIP to shadow syscall page to continue execution
		spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
		gcpustate_vmrwp->value = sl_syscall_shadowpage_vaddr | ((uint32_t)gpa & 0x00000FFFUL);
		ugcpust_slab_main(&spl);

		_XDPRINTF_("%s[%u]: syscall trapping reset eip to 0x%08x\n",
		__func__, (uint16_t)cpuindex, gcpustate_vmrwp->value);

		return true;
	}else{
		//do nothing
		//@ghost sysclog_loginfo_nwlogged = false;
		return false;
	}

}

