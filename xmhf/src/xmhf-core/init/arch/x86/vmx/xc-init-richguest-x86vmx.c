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

// XMHF rich guest -- initialization portion, x86 (VMX) backend implementation
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf-core.h> 
#include <xc-x86.h>
#include <xc-x86vmx.h>

//setup guest OS state for the partition
void xmhf_richguest_arch_setupguestOSstate(context_desc_t context_desc){
	xc_hypapp_arch_param_t ap;
	
	//--------------------------------------------------------------------------------------------------------------------------------
	//setup guest state
	//CR0, real-mode, PE and PG bits cleared
	ap = xc_api_cpustate_get(context_desc, XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS);
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS;
	ap.param.controlregs.cr0 = ap.param.controlregs.cr0 & ~(CR0_PE) & ~(CR0_PG);
	ap.param.controlregs.cr3 = 0;
	xc_api_cpustate_set(context_desc, ap);
	
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS;
	ap.param.cpugprs.eax = 0;
	ap.param.cpugprs.ebx = 0;
	ap.param.cpugprs.ecx = 0;
	ap.param.cpugprs.edx = 0x80;
	ap.param.cpugprs.esi = 0;
	ap.param.cpugprs.edi = 0;
	ap.param.cpugprs.ebp = 0;
	ap.param.cpugprs.esp = 0;
	xc_api_cpustate_set(context_desc, ap);
							

	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY;
	ap.param.activity.rflags = ((((0 & ~((1<<3)|(1<<5)|(1<<15)) ) | (1 <<1)) | (1<<9)) & ~(1<<14));
	if(context_desc.cpu_desc.isbsp){
		ap.param.activity.rip = 0x7c00;
		ap.param.activity.activity_state = 0;	//normal activity state
	}else{
		ap.param.activity.rip = 0;
		ap.param.activity.activity_state = 3;	//wait-for-SIPI
	}
	ap.param.activity.interruptibility=0;
	xc_api_cpustate_set(context_desc, ap);

	
	ap.operation = XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC;
	//CS, DS, ES, FS, GS and SS segments
	ap.param.desc.cs.selector 		 = 0  ;
	ap.param.desc.cs.base 			 = 0  ;
	ap.param.desc.cs.limit 			 = 0xFFFF  ;
	ap.param.desc.cs.access_rights 	 = 0x93  ;	
	ap.param.desc.ds.selector 		 = 0  ;
	ap.param.desc.ds.base 			 = 0  ;
	ap.param.desc.ds.limit 			 = 0xFFFF  ;
	ap.param.desc.ds.access_rights 	 = 0x93  ;	
	ap.param.desc.es.selector 		 = 0  ;
	ap.param.desc.es.base 			 = 0  ;
	ap.param.desc.es.limit 			 = 0xFFFF  ;
	ap.param.desc.es.access_rights 	 = 0x93  ;	
	ap.param.desc.fs.selector 		 = 0  ;
	ap.param.desc.fs.base 			 = 0  ;
	ap.param.desc.fs.limit 			 = 0xFFFF  ;
	ap.param.desc.fs.access_rights 	 = 0x93  ;	
	ap.param.desc.gs.selector 		 = 0  ;
	ap.param.desc.gs.base 			 = 0  ;
	ap.param.desc.gs.limit 			 = 0xFFFF  ;
	ap.param.desc.gs.access_rights 	 = 0x93  ;	
	ap.param.desc.ss.selector 		 = 0  ;
	ap.param.desc.ss.base	 		 = 0  ;
	ap.param.desc.ss.limit 			 = 0xFFFF  ;
	ap.param.desc.ss.access_rights 	 = 0x93  ;	
	//IDTR                             
	ap.param.desc.idtr.base			 = 0  ;
	ap.param.desc.idtr.limit 		 = 0x3ff  ;
	//GDTR                             
	ap.param.desc.gdtr.base			 = 0  ;
	ap.param.desc.gdtr.limit 		 = 0  ;
	//LDTR); unusable                  
	ap.param.desc.ldtr.base			 = 0  ;
	ap.param.desc.ldtr.limit 		 = 0  ;
	ap.param.desc.ldtr.selector		 = 0  ;
	ap.param.desc.ldtr.access_rights = 0x10000 ; 
	//TR); should be usable for VMX to work; not used by guest
	ap.param.desc.tr.base 			 = 0  ;	
	ap.param.desc.tr.limit 			 = 0  ;	
	ap.param.desc.tr.selector 		 = 0  ;	
	ap.param.desc.tr.access_rights 	 = 0x83  ; 	
	xc_api_cpustate_set(context_desc, ap);

}
