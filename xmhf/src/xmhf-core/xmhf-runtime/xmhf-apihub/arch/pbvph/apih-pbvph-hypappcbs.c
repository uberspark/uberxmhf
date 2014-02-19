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

/*
 * 	apih-hypappcbs.c
 * 
 *  XMHF core hypapp callback interfaces
 * 
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */


// hypapp main (initialization) function
//u32 xmhfhypapp_main(__xmhfattribute__(core-rw) APP_PARAM_BLOCK *apb){
u32 xmhfhypapp_main(hypapp_env_block_t hypappenvb){
	u32 result;
	
	//paramcore->param1 = (u32)apb;
	//memcpy((void *)&paramcore->apb, apb, sizeof(APP_PARAM_BLOCK));
	paramcore->hypappenvb = hypappenvb;
	xmhf_apihub_arch_tohypapp(XMHF_APIHUB_HYPAPPCB_MAIN);
	result = (u32)paramhypapp->result;
	
	return result;
}

//hypapp hypercall handler
//returns APP_SUCCESS if we handled the hypercall else APP_ERROR
//u32 xmhfhypapp_handlehypercall(__xmhfattribute__(core-rw) VCPU *vcpu, u32 callno, __xmhfattribute__(core-rw) struct regs *r){
u32 xmhfhypapp_handlehypercall(context_desc_t context_desc, u64 hypercall_id, u64 hypercall_param){
	u32 result;
	
	//paramcore->param1 = (u32)vcpu;
	//paramcore->param2 = (u32)callno;
	//paramcore->param3 = (u32)r;
	//memcpy((void *)&paramcore->vcpu, vcpu, sizeof(VCPU));
	//memcpy((void *)&paramcore->r, r, sizeof(struct regs));
	paramcore->context_desc = context_desc;
	paramcore->param1 = hypercall_id;
	paramcore->param2 = hypercall_param;
	
	xmhf_apihub_arch_tohypapp(XMHF_APIHUB_HYPAPPCB_HYPERCALL);
	result = (u32)paramhypapp->result;
	
	return result;	
}


//handles XMHF shutdown callback
//note: should not return
void xmhfhypapp_handleshutdown(context_desc_t context_desc){
	u32 result;
	
	//paramcore->param1 = (u32)vcpu;
	//paramcore->param2 = (u32)r;
	paramcore->context_desc = context_desc;
	//memcpy((void *)&paramcore->vcpu, vcpu, sizeof(VCPU));
	//memcpy((void *)&paramcore->r, r, sizeof(struct regs));
	xmhf_apihub_arch_tohypapp(XMHF_APIHUB_HYPAPPCB_SHUTDOWN);
	
	printf("\n%s: should never get here. halting!", __FUNCTION__);
	HALT();	
}


//handles h/w pagetable violations
//for now this always returns APP_SUCCESS
u32 xmhfhypapp_handleintercept_hwpgtblviolation(context_desc_t context_desc, u64 gpa, u64 gva, u64 error_code){
	u32 result;
	
	paramcore->context_desc = context_desc;
	paramcore->param1 = gpa;
	paramcore->param2 = gva;
	paramcore->param3 = error_code;
	//memcpy((void *)&paramcore->vcpu, vcpu, sizeof(VCPU));
	//memcpy((void *)&paramcore->r, r, sizeof(struct regs));
	xmhf_apihub_arch_tohypapp(XMHF_APIHUB_HYPAPPCB_HWPGTBLVIOLATION);
	result = (u32)paramhypapp->result;
	
	return result;	

}


//handles i/o port intercepts
//returns either APP_IOINTERCEPT_SKIP or APP_IOINTERCEPT_CHAIN
u32 xmhfhypapp_handleintercept_portaccess(context_desc_t context_desc, u32 portnum, u32 access_type, u32 access_size){

	u32 result;
	
	paramcore->context_desc = context_desc;
	paramcore->param1 = (u32)portnum;
	paramcore->param2 = (u32)access_type;
	paramcore->param3 = (u32)access_size;
	//memcpy((void *)&paramcore->vcpu, vcpu, sizeof(VCPU));
	//memcpy((void *)&paramcore->r, r, sizeof(struct regs));
	xmhf_apihub_arch_tohypapp(XMHF_APIHUB_HYPAPPCB_PORTACCESS);
	result = (u32)paramhypapp->result;
	
	return result;	

}

