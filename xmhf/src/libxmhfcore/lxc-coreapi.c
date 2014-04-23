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

#include <xmhf.h>
#include <xmhf-core.h>

/*
 * XMHF core API calls that hypapps rely on
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

extern void libxmhfcore_hypapptocore(u32 callnum);


// xmhfc_puts -- to output debug string 
void xmhfcore_outputdebugstring(__xmhfattribute__(hypapp-rw) const char *s __attribute__((unused))){
	paramhypapp->param1 = (u32)s;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_OUTPUTDEBUGSTRING);

	return;
}

// xmhf_baseplatform_reboot -- reboot 
void xmhfcore_reboot(context_desc_t context_desc){
	//paramhypapp->param1 = (u32)vcpu;
	paramhypapp->context_desc = context_desc;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_REBOOT);

	return;
}

//xmhf_memprot_setprot -- setmemprot
void xmhfcore_setmemprot(context_desc_t context_desc, u64 gpa, u32 prottype){

	paramhypapp->context_desc = context_desc;
	paramhypapp->param1 = (u64)gpa;
	paramhypapp->param2 = (u32)prottype;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_SETMEMPROT);
	return;
}

//void xmhfcore_memprot_flushmappings(VCPU *vcpu);
void xmhfcore_memprot_flushmappings(context_desc_t context_desc){
	paramhypapp->context_desc = context_desc;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_MEMPROT_FLUSHMAPPINGS);
	return;
}	

//u8 * xmhf_smpguest_walk_pagetables(VCPU *vcpu, u32 vaddr);
u8 * xmhfcore_smpguest_walk_pagetables(context_desc_t context_desc, u32 vaddr){
	u8 *result;
	paramhypapp->context_desc = context_desc;
	paramhypapp->param1 = (u32)vaddr;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_SMPGUEST_WALK_PAGETABLES);
	result = (u8 *)(u32)paramcore->result;
	return result;
}


void xmhfcore_memprot_hpt_setentry(context_desc_t context_desc, u64 hpt_paddr, u64 entry){
	u64 result;
	paramhypapp->context_desc = context_desc;
	paramhypapp->param1 = hpt_paddr;
	paramhypapp->param2 = entry;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_HPT_SETENTRY);
	return;
}


//HPT related core APIs
void xc_api_hpt_setprot(context_desc_t context_desc, u64 gpa, u32 prottype){
	libxmhfcore_hypapptocore(XC_API_HPT_SETPROT);
}

u32 xc_api_hpt_getprot(context_desc_t context_desc, u64 gpa){
	libxmhfcore_hypapptocore(XC_API_HPT_GETPROT);
	return 0;
}

void xc_api_hpt_setentry(context_desc_t context_desc, u64 gpa, u64 entry){
	libxmhfcore_hypapptocore(XC_API_HPT_SETENTRY);
	
}

u64 xc_api_hpt_getentry(context_desc_t context_desc, u64 gpa){
	libxmhfcore_hypapptocore(XC_API_HPT_GETENTRY);
	return 0;
}

void xc_api_hpt_flushcaches(context_desc_t context_desc){
	libxmhfcore_hypapptocore(XC_API_HPT_FLUSHCACHES);

}

void xc_api_hpt_flushcaches_smp(context_desc_t context_desc){
	libxmhfcore_hypapptocore(XC_API_HPT_FLUSHCACHES_SMP);
	
}

u64 xc_api_hpt_lvl2pagewalk(context_desc_t context_desc, u64 gva){
	libxmhfcore_hypapptocore(XC_API_HPT_LVL2PAGEWALK);
	return 0;
}


