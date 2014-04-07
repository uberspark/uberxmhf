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

/*//void xmhfcore_memprot_getprot(VCPU *vcpu, u64 gpa)
u32 xmhfcore_memprot_getprot(__xmhfattribute__(core-ro) VCPU *vcpu, u64 gpa){
	u32 result;
	paramhypapp->param1 = (u32)vcpu;
	paramhypapp->param2 = (u64)gpa;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_MEMPROT_GETPROT);
	result = (u32)paramcore->result;
	return result;
}*/

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

/*									   
u64 xmhfcore_memprot_arch_x86svm_get_h_cr3(__xmhfattribute__(core-ro) VCPU *vcpu){
	u64 result;
	paramhypapp->param1 = (u32)vcpu;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_MEMPROT_ARCH_X86SVM_GET_H_CR3);
	result = (u64)paramcore->result;
	return result;
}

void xmhfcore_memprot_arch_x86svm_set_h_cr3(__xmhfattribute__(core-ro) VCPU *vcpu, u64 n_cr3){
	paramhypapp->param1 = (u32)vcpu;
	paramhypapp->param2 = (u64)n_cr3;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_MEMPROT_ARCH_X86SVM_SET_H_CR3);
	return;
}*/

/*u64 xmhfcore_memprot_arch_x86vmx_get_EPTP(__xmhfattribute__(core-ro) VCPU *vcpu){
	u64 result;
	paramhypapp->param1 = (u32)vcpu;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_MEMPROT_ARCH_X86VMX_GET_EPTP);
	result = (u64)paramcore->result;
	return result;
}


void xmhfcore_memprot_arch_x86vmx_set_EPTP(__xmhfattribute__(core-ro) VCPU *vcpu, u64 eptp){
	paramhypapp->param1 = (u32)vcpu;
	paramhypapp->param2 = (u64)eptp;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_MEMPROT_ARCH_X86VMX_SET_EPTP);
	return;
}*/

/*xmhfcoreapiretval_t xmhfcore_baseplatform_getcputable(void){
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_BASEPLATFORM_GETCPUTABLE);
	return paramcore->retval;
}*/	

void xmhfcore_memprot_setsingularhpt(u64 hpt){
	paramhypapp->param1 = (u64)hpt;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_MEMPROT_SETSINGULARHPT);
	return;
}

u64 xmhfcore_memprot_getHPTroot(context_desc_t context_desc){
	u64 result;
	paramhypapp->context_desc = context_desc;
	//paramhypapp->param1 = (u32)vcpu;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_MEMPROT_GETHPTROOT);
	result = (u64)paramcore->result;
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


/*

//void xmhfcore_partition_legacyIO_setprot(VCPU *vcpu, u32 port, u32 size, u32 prottype);
void xmhfcore_partition_legacyIO_setprot(__xmhfattribute__(core-ro) VCPU *vcpu, u32 port, u32 size, u32 prottype){
	paramhypapp->param1 = (u32)vcpu;
	paramhypapp->param2 = (u32)port;
	paramhypapp->param3 = (u32)size;
	paramhypapp->param4 = (u32)prottype;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_PARTITION_LEGACYIO_SETPROT);
	return;
}	


int xmhfcore_tpm_open_locality(int locality){
	int result;
	paramhypapp->param1 = (u32)locality;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_TPM_OPEN_LOCALITY);
	result = (int)paramcore->result;
	return result;
}

void xmhfcore_tpm_deactivate_all_localities(void){
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_TPM_DEACTIVATE_ALL_LOCALITIES);
	return;
}	


//XXX: TODO: need to rework to handle pointer parameters properly	
uint32_t xmhfcore_tpm_write_cmd_fifo(uint32_t locality, uint8_t *in,
                                   uint32_t in_size, uint8_t *out,
                                   uint32_t *out_size){
	uint32_t result;
	paramhypapp->param1 = (u32)locality;
	paramhypapp->param2 = (u32)in;
	paramhypapp->param3 = (u32)in_size;
	paramhypapp->param4 = (u32)out;
	paramhypapp->param5 = (u32)out_size;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_TPM_WRITE_CMD_FIFO);
	result = (uint32_t)paramcore->result;
	return result;
}									   

//u32 xmhfcore_baseplatform_arch_x86_acpi_getRSDP(ACPI_RSDP *rsdp);
//TODO: need to rework such that we return a pointer to the rsdp which
//is in core area
u32 xmhfcore_baseplatform_arch_x86_acpi_getRSDP(ACPI_RSDP *rsdp){
	u32 result;
	paramhypapp->param1 = (u32)rsdp;
	libxmhfcore_hypapptocore(XMHF_APIHUB_COREAPI_BASEPLATFORM_ARCH_X86_ACPI_GETRSDP);
	result = (u32)paramcore->result;
	return result;
}	
*/
