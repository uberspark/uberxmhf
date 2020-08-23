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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <xmhfgeec.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_nwlog.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_gcpustate.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uapi_slabmempgtbl.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xh_syscalllog.h>

//register a syscall handler code page (at gpa)
void sysclog_register(uint32_t cpuindex, uint32_t guest_slab_index, uint32_t syscall_page_paddr, uint32_t syscall_shadowpage_vaddr, uint32_t syscall_shadowpage_paddr){

	slab_params_t spl;
	xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp =
	(xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *)spl.in_out_params;
	xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
	(xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;
	xmhfgeec_uapi_slabmempgtbl_flushtlb_params_t *flushtlbp =
		(xmhfgeec_uapi_slabmempgtbl_flushtlb_params_t *)spl.in_out_params;


	_XDPRINTF_("%s[%u]: gid=%u, syscall_page_paddr=0x%08x\n",
				__func__, (uint16_t)cpuindex, guest_slab_index, syscall_page_paddr);
	_XDPRINTF_("%s[%u]: syscall_shadowpage_vaddr=0x%08x, syscall_shadowpage_paddr=0x%08x\n",
				__func__, (uint16_t)cpuindex, syscall_shadowpage_vaddr, syscall_shadowpage_paddr);

	spl.src_slabid = XMHFGEEC_SLAB_XH_SYSCALLLOG;
	spl.cpuid = cpuindex;
	spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;

	spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR;
	getentryforpaddrp->dst_slabid = guest_slab_index;
	getentryforpaddrp->gpa = syscall_page_paddr;
	getentryforpaddrp->result_entry = 0;
	XMHF_SLAB_CALLNEW(&spl);
	_XDPRINTF_("%s[%u]: syscall_page existing entry = 0x%08x\n",
				__func__, (uint16_t)cpuindex, (uint32_t)getentryforpaddrp->result_entry);

	 spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
	setentryforpaddrp->dst_slabid = guest_slab_index;
	setentryforpaddrp->gpa = syscall_page_paddr;
	setentryforpaddrp->entry = getentryforpaddrp->result_entry & ~(0x4);
	XMHF_SLAB_CALLNEW(&spl);
	_XDPRINTF_("%s[%u]: syscall_page new entry = 0x%08x\n",
				__func__, (uint16_t)cpuindex, (uint32_t)setentryforpaddrp->entry);

	//flush EPT TLB for permission changes to take effect
	spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_FLUSHTLB;
	flushtlbp->dst_slabid = guest_slab_index;
	XMHF_SLAB_CALLNEW(&spl);

	//initialize network comms
	spl.src_slabid = XMHFGEEC_SLAB_XH_SYSCALLLOG;
	spl.dst_slabid = XMHFGEEC_SLAB_XC_NWLOG;
	spl.cpuid = cpuindex;
	spl.dst_uapifn = XMHFGEEC_SLAB_XC_NWLOG_INITIALIZE;
	XMHF_SLAB_CALLNEW(&spl);

	sl_syscall_page_paddr = syscall_page_paddr;
	sl_syscall_shadowpage_vaddr = syscall_shadowpage_vaddr;
	sl_activated=true;
}


