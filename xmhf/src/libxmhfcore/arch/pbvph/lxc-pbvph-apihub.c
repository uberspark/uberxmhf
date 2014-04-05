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

// hypapp-startup.c
// hypapp C startup function 
// author: amit vasudevan (amitvasudevan@acm.org)

extern XMHF_HYPAPP_HEADER __attribute__((section (".hypapp_header_data"))) hypappheader ;

//----------------------------------------------------------------------
// all control transfers to the hypapp space from the core 
// are handled via this interface
//----------------------------------------------------------------------
void libxmhfcore_hypappfromcore(u32 callnum){
	
	printf("\n%s: starting, callnum=%u...", __FUNCTION__, callnum);

	switch(callnum){
			case XMHF_APIHUB_HYPAPPCB_MAIN:{
					//paramhypapp->result=xmhf_app_main( (VCPU *)(u32)paramcore->param1, (APP_PARAM_BLOCK *)(u32)paramcore->param2);
					//paramhypapp->result=xmhf_app_main((APP_PARAM_BLOCK *)(u32)paramcore->param1);
					//paramhypapp->result=xmhf_app_main((APP_PARAM_BLOCK *)&paramcore->apb);
					paramhypapp->result=xmhf_app_main(paramcore->hypappenvb);
					break;
				}
			
			case XMHF_APIHUB_HYPAPPCB_HYPERCALL:{
					//paramhypapp->result=xmhf_app_handlehypercall( (VCPU *)(u32)paramcore->param1, (u32)paramcore->param2, (struct regs *)(u32)paramcore->param3);
					//paramhypapp->result=xmhf_app_handlehypercall( (VCPU *)&paramcore->vcpu, (u32)paramcore->param2, (struct regs *)(u32)paramcore->param3);
					//paramhypapp->result=xmhf_app_handlehypercall( (VCPU *)&paramcore->vcpu, (u32)paramcore->param2, (struct regs *)&paramcore->r);
					paramhypapp->result=xmhf_app_handlehypercall( paramcore->context_desc, paramcore->param1, paramcore->param2);
					
					break;
				}

			case XMHF_APIHUB_HYPAPPCB_SHUTDOWN:{
					//xmhf_app_handleshutdown( (VCPU *)(u32)paramcore->param1, (struct regs *)(u32)paramcore->param2);
					xmhf_app_handleshutdown( paramcore->context_desc );
					break;
				}

			case XMHF_APIHUB_HYPAPPCB_HWPGTBLVIOLATION:{
					//paramhypapp->result=xmhf_app_handleintercept_hwpgtblviolation( (VCPU *)(u32)paramcore->param1, (struct regs *)(u32)paramcore->param2, 
					//			paramcore->param3, paramcore->param4, paramcore->param5);
					paramhypapp->result=xmhf_app_handleintercept_hwpgtblviolation( paramcore->context_desc, paramcore->param1, paramcore->param2, paramcore->param3);

					break;
				}

			case XMHF_APIHUB_HYPAPPCB_PORTACCESS:{
					//paramhypapp->result=xmhf_app_handleintercept_portaccess( (VCPU *)(u32)paramcore->param1, (struct regs *)(u32)paramcore->param2, 
					//			paramcore->param3, paramcore->param4, paramcore->param5);
					paramhypapp->result=xmhf_app_handleintercept_portaccess( paramcore->context_desc, paramcore->param1, paramcore->param2, paramcore->param3);

					break;
				}
			
			default:
				printf("\n%s: WARNING, unsupported hypapp call (%u), returning", __FUNCTION__, callnum);
				break;
	}

	return;	//back to core
}

/*//----------------------------------------------------------------------
// all control transfers to the core space from the hypapp 
// are handled via this interface
//----------------------------------------------------------------------
void libxmhfcore_hypapptocore(u32 callnum){
	typedef void (*HYPAPPTOCORE)(u32 callnum);
	HYPAPPTOCORE hypapptocore = (HYPAPPTOCORE)hypappheader.addr_hypapptocore;
	hypapptocore(callnum); //to the core
	return; //back from the core
}*/

