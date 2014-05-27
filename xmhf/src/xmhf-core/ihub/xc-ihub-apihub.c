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

#include <xmhf-core.h>

#include <xc-x86.h>
#include <xc-x86vmx.h>

/*
 * 	xc-apihub - runtime arch. independent portion
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */


//function where we get control when hypapp tries to invoke a function in
//the core
void xmhf_apihub_fromhypapp(u32 callnum){
	printf("\n%s: starting, callnum=%u...", __FUNCTION__, callnum);
	
	//if paramhypapp->param1 is of type VCPU * then it basically points to paramcore->vcpu, the original vcpu data structure is in paramcore->param1
	switch(callnum){
			case XC_API_HPT_SETPROT:{
				xc_api_hpt_setprot(paramhypapp->context_desc, (u64)paramhypapp->param1, (u32)paramhypapp->param2);
				break;
			}

			case XC_API_HPT_GETPROT:{
				paramcore->result = xc_api_hpt_getprot(paramhypapp->context_desc, (u64)paramhypapp->param1);
				break;
			}

			case XC_API_HPT_SETENTRY:{
				xc_api_hpt_setentry(paramhypapp->context_desc, (u64)paramhypapp->param1, (u64)paramhypapp->param2);
				break;
			}

			case XC_API_HPT_GETENTRY:{
				paramcore->result = xc_api_hpt_getentry(paramhypapp->context_desc, (u64)paramhypapp->param1);
				break;
			}

			case XC_API_HPT_FLUSHCACHES:{
				xc_api_hpt_flushcaches(paramhypapp->context_desc);
				break;
			}

			case XC_API_HPT_FLUSHCACHES_SMP:{
				xc_api_hpt_flushcaches_smp(paramhypapp->context_desc);
				break;
			}

			case XC_API_HPT_LVL2PAGEWALK:{ 
				paramcore->result = xc_api_hpt_lvl2pagewalk(paramhypapp->context_desc, (u64)paramhypapp->param1);
				break;
			}
				
				
			case XC_API_TRAPMASK_SET:{
				xc_api_trapmask_set(paramhypapp->context_desc, paramhypapp->xc_hypapp_arch_param);	
				break;
			}

			case XC_API_TRAPMASK_CLEAR:{
				xc_api_trapmask_clear(paramhypapp->context_desc, paramhypapp->xc_hypapp_arch_param);	
				break;
			}
	

			case XC_API_CPUSTATE_SET:{
				xc_api_cpustate_set(paramhypapp->context_desc, paramhypapp->xc_hypapp_arch_param);	
				break;
			}

			case XC_API_CPUSTATE_GET:{
				xc_api_cpustate_get(paramhypapp->context_desc, paramhypapp->param1);	
				break;
			}
			
	
	
			case XMHF_APIHUB_COREAPI_OUTPUTDEBUGSTRING:{	//void xmhfc_puts(...)
					extern void xmhfc_puts(const char *s);	//TODO: move this into an appropriate header
					xmhfc_puts( __xmhfattribute__(hypapp-ro) (char *)(u32)paramhypapp->param1 );
					break;
				}
				
			case XMHF_APIHUB_COREAPI_REBOOT:{	//void xmhf_baseplatform_reboot(...)
					xc_api_platform_shutdown(paramhypapp->context_desc );
					printf("\n%s: xmhf_baseplatform_reboot should never return. halting!", __FUNCTION__);
					HALT();
					break;
				}

			//case XMHF_APIHUB_COREAPI_SETMEMPROT:{ //void xmhf_memprot_setprot(...)
			//	xmhf_memprot_setprot(paramhypapp->context_desc, (u64)paramhypapp->param1, (u32)paramhypapp->param2);
			//	break;
			//}
			
			//case XMHF_APIHUB_COREAPI_MEMPROT_FLUSHMAPPINGS:{ //void xmhfcore_memprot_flushmappings(...);
			//	xmhf_memprot_flushmappings( paramhypapp->context_desc );
			//	break;
			//}
			
			//case XMHF_APIHUB_COREAPI_SMPGUEST_WALK_PAGETABLES:{ //u8 * xmhf_smpguest_walk_pagetables(...);
			//	paramcore->result = (u32)xmhf_smpguest_walk_pagetables( paramhypapp->context_desc, (u32)paramhypapp->param1);
			//	break;
			//}
			
			//case XMHF_APIHUB_COREAPI_HPT_SETENTRY:{ //void xmhf_memprot_hpt_setentry(...)
			//	xmhf_memprot_hpt_setentry(paramhypapp->context_desc, paramhypapp->param1, paramhypapp->param2);
			//	break;
			//}

			default:
				printf("\n%s: WARNING, unsupported core API call (%u), returning", __FUNCTION__, callnum);
				break;
	}

	return;	//back to hypapp
}




//----------------------------------------------------------------------
/*
 * 	apih-hypappcbs.c
 * 
 *  XMHF core hypapp callback interfaces
 * 
 *  author: amit vasudevan (amitvasudevan@acm.org)
 */


// hypapp main (initialization) function
u32 xc_hypapp_initialization(context_desc_t context_desc, hypapp_env_block_t hypappenvb){
	u32 result;
	/*context_desc_t context_desc;
	
	context_desc.partition_desc.partitionid = xc_cpu->parentpartition->partitionid;
	context_desc.cpu_desc.cpuid = xc_cpu->cpuid;
	context_desc.cpu_desc.isbsp = xc_cpu->is_bsp;
	context_desc.cpu_desc.xc_cpu = xc_cpu;*/

	paramcore->context_desc = context_desc;
	paramcore->hypappenvb = hypappenvb;
	xmhf_apihub_arch_tohypapp(XMHF_APIHUB_HYPAPPCB_INITIALIZATION);
	result = (u32)paramhypapp->result;
	
	return result;
}

//hypapp hypercall handler
//returns APP_SUCCESS if we handled the hypercall else APP_ERROR
u32 xc_hypapp_handlehypercall(context_desc_t context_desc, u64 hypercall_id, u64 hypercall_param){
	u32 result;
	/*context_desc_t context_desc;
	
	context_desc.partition_desc.partitionid = xc_cpu->parentpartition->partitionid;
	context_desc.cpu_desc.cpuid = xc_cpu->cpuid;
	context_desc.cpu_desc.isbsp = xc_cpu->is_bsp;
	context_desc.cpu_desc.xc_cpu = xc_cpu;*/
	
	paramcore->context_desc = context_desc;
	paramcore->param1 = hypercall_id;
	paramcore->param2 = hypercall_param;
	
	xmhf_apihub_arch_tohypapp(XMHF_APIHUB_HYPAPPCB_HYPERCALL);
	result = (u32)paramhypapp->result;
	
	return result;	
}


//handles XMHF shutdown callback
//note: should not return
void xc_hypapp_handleshutdown(context_desc_t context_desc){
	u32 result;
	/*context_desc_t context_desc;

	context_desc.partition_desc.partitionid = xc_cpu->parentpartition->partitionid;
	context_desc.cpu_desc.cpuid = xc_cpu->cpuid;
	context_desc.cpu_desc.isbsp = xc_cpu->is_bsp;
	context_desc.cpu_desc.xc_cpu = xc_cpu;*/
	
	paramcore->context_desc = context_desc;
	xmhf_apihub_arch_tohypapp(XMHF_APIHUB_HYPAPPCB_SHUTDOWN);
	
	printf("\n%s: should never get here. halting!", __FUNCTION__);
	HALT();	
}


//handles h/w pagetable violations
//for now this always returns APP_SUCCESS
u32 xc_hypapp_handleintercept_hptfault(context_desc_t context_desc, u64 gpa, u64 gva, u64 error_code){
	u32 result;
	/*context_desc_t context_desc;
	
	context_desc.partition_desc.partitionid = xc_cpu->parentpartition->partitionid;
	context_desc.cpu_desc.cpuid = xc_cpu->cpuid;
	context_desc.cpu_desc.isbsp = xc_cpu->is_bsp;
	context_desc.cpu_desc.xc_cpu = xc_cpu;*/

	paramcore->context_desc = context_desc;
	paramcore->param1 = gpa;
	paramcore->param2 = gva;
	paramcore->param3 = error_code;
	xmhf_apihub_arch_tohypapp(XMHF_APIHUB_HYPAPPCB_HPTFAULT);
	result = (u32)paramhypapp->result;
	
	return result;	

}


//handles trap intercepts
//returns either APP_TRAP_SKIP or APP_TRAP_CHAIN
u32 xc_hypapp_handleintercept_trap(context_desc_t context_desc, xc_hypapp_arch_param_t xc_hypapp_arch_param){
	u32 result;
	/*context_desc_t context_desc;

	context_desc.partition_desc.partitionid = xc_cpu->parentpartition->partitionid;
	context_desc.cpu_desc.cpuid = xc_cpu->cpuid;
	context_desc.cpu_desc.isbsp = xc_cpu->is_bsp;
	context_desc.cpu_desc.xc_cpu = xc_cpu;*/
	
	paramcore->context_desc = context_desc;
	paramcore->xc_hypapp_arch_param = xc_hypapp_arch_param;
	xmhf_apihub_arch_tohypapp(XMHF_APIHUB_HYPAPPCB_TRAP);
	result = (u32)paramhypapp->result;
	
	return result;	

}

