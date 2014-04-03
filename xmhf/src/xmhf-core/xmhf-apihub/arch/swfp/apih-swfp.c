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
 * 	apih-swfp.c
 * 
 *  XMHF core API interface component software function-pointer backend
 * 
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */



XMHF_HYPAPP_HEADER *hypappheader=(XMHF_HYPAPP_HEADER *)__TARGET_BASE_XMHFHYPAPP;

// the list of core APIs
u32 swfp_coreapis[] = {
		(u32)&xmhfc_puts,
		(u32)&xmhf_baseplatform_reboot,
		(u32)&xmhf_memprot_setprot,
		(u32)&xmhf_memprot_getprot,
		(u32)&xmhf_memprot_flushmappings,
		(u32)&xmhf_smpguest_walk_pagetables,
		(u32)&xmhf_partition_legacyIO_setprot,
		(u32)&xmhf_baseplatform_arch_x86_acpi_getRSDP,
		(u32)&xmhf_tpm_open_locality,
		(u32)&xmhf_tpm_deactivate_all_localities,
		(u32)&tpm_write_cmd_fifo,
		(u32)&xmhf_memprot_arch_x86svm_get_h_cr3,
		(u32)&xmhf_memprot_arch_x86svm_set_h_cr3,
		(u32)&xmhf_memprot_arch_x86vmx_get_EPTP,
		(u32)&xmhf_memprot_arch_x86vmx_set_EPTP,
		(u32)&xmhf_baseplatform_getcputable,
		0,
};


// function pointer based backend does not need the arch_tohypapp
// definition

// void xmhf_apihub_arch_tohypapp(u32 hypappcallnum, __attribute__((unused)) void *args){
//}


// function pointer based backend does not need the arch_fromhypapp
// definition

//void xmhf_apihub_arch_fromhypapp(u32 callnum, void * args __attribute__((unused)) ){
//}


// initialization function for the backend
void xmhf_apihub_arch_initialize (void){
	
	printf("\n%s: starting...", __FUNCTION__);
	printf("\n%s: hypappheader at %08x", __FUNCTION__, hypappheader);
	printf("\n%s: hypappheader->magic is %08x", __FUNCTION__, hypappheader->magic);
	printf("\n%s: hypappheader->addr_hypappfromcore is %08x", __FUNCTION__, hypappheader->addr_hypappfromcore);
	
	//cast hypapp header information into hypappheader 
	//(a data structure of type XMHF_HYPAPP_HEADER) and populate the
	//hypapp parameter block field
	{
		hypappheader->apb.bootsector_ptr = (u32)rpb->XtGuestOSBootModuleBase;
		hypappheader->apb.bootsector_size = (u32)rpb->XtGuestOSBootModuleSize;
		hypappheader->apb.optionalmodule_ptr = (u32)rpb->runtime_appmodule_base;
		hypappheader->apb.optionalmodule_size = (u32)rpb->runtime_appmodule_size;
		hypappheader->apb.runtimephysmembase = (u32)rpb->XtVmmRuntimePhysBase;  
		strncpy(hypappheader->apb.cmdline, rpb->cmdline, sizeof(hypappheader->apb.cmdline));
		printf("\n%s: sizeof(XMHF_HYPAPP_HEADER)=%u", __FUNCTION__, sizeof(XMHF_HYPAPP_HEADER));
		printf("\n%s: sizeof(APP_PARAM_BLOCK)=%u", __FUNCTION__, sizeof(APP_PARAM_BLOCK));
			
	}

	hypappheader->addr_hypapptocore = 0;

	//debug dump the core API table
	{
		u32 index=0;
		printf("\n%s: dumping sfwp_coreapis table...", __FUNCTION__);
		while(swfp_coreapis[index] != 0){
			printf("\n  %08x", swfp_coreapis[index]);
			index++;
		}
		printf("\n%s: dumped %u entries", __FUNCTION__, index);
	}

	
	{
		//obtain the address of the table containing the pointers to
		//the core APIs and fill them out for the hypapp
		u32 *coreapitableptrs = (u32 *)hypappheader->optionalparam1;
		u32 index=0;
		
		printf("\n%s: preparing to populate hypapp core API pointer table entries at %08x...", __FUNCTION__, coreapitableptrs);
		while(coreapitableptrs[index] != 0){
				* ((u32 *)coreapitableptrs[index]) = swfp_coreapis[index];
				printf("\n  wrote %08x at address %08x", swfp_coreapis[index], coreapitableptrs[index]);
				index++;
		}
		
		printf("\n%s: stored %u core API entries", __FUNCTION__, index);
	}
	
	
	//dump the pointer to the hypapp callback table in the hypapp 
	//header optionalparam2 and initialize the hypapp callback
	//function pointers
	{
		u32 *hypappcbtable = (u32 *)hypappheader->optionalparam2;
		printf("\n%s: hypapp callback table at %08x", __FUNCTION__, hypappcbtable);
		
		xmhfhypapp_main = (XMHFAPPMAIN)hypappcbtable[XMHF_APIHUB_HYPAPPCB_MAIN];
		xmhfhypapp_handlehypercall = (XMHFAPPHANDLEHYPERCALL)hypappcbtable[XMHF_APIHUB_HYPAPPCB_HYPERCALL];
		xmhfhypapp_handleshutdown = (XMHFAPPHANDLESHUTDOWN)hypappcbtable[XMHF_APIHUB_HYPAPPCB_SHUTDOWN];
		xmhfhypapp_handleintercept_hwpgtblviolation = (XMHFAPPHANDLEINTERCEPTHWPGTBLVIOLATION)hypappcbtable[XMHF_APIHUB_HYPAPPCB_HWPGTBLVIOLATION];
		xmhfhypapp_handleintercept_portaccess = (XMHFAPPHANDLEINTERCEPTPORTACCESS)hypappcbtable[XMHF_APIHUB_HYPAPPCB_PORTACCESS];
		
		printf("\n%s: hypapp callbacks...", __FUNCTION__);
		printf("\n  xmhfhypapp_main=%08x", (u32)xmhfhypapp_main);
		printf("\n  xmhfhypapp_handlehypercall=%08x", (u32)xmhfhypapp_handlehypercall);
		printf("\n  xmhfhypapp_handleshutdown=%08x", (u32)xmhfhypapp_handleshutdown);
		printf("\n  xmhfhypapp_handleintercept_hwpgtblviolation=%08x", (u32)xmhfhypapp_handleintercept_hwpgtblviolation);
		printf("\n  xmhfhypapp_handleintercept_portaccess=%08x", (u32)xmhfhypapp_handleintercept_portaccess);
		
	}
	
}
