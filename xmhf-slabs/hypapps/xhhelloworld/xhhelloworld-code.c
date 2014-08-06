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

// hello world hypapp main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xhhelloworld.h>
#include <xcapi.h>

#define HELLOWORLD_PING					0xC0

// hypapp initialization
u32 xmhf_hypapp_initialization(context_desc_t context_desc, hypapp_env_block_t hypappenvb){	
	_XDPRINTF_("\nCPU %u: helloworld initialized", context_desc.cpu_desc.cpu_index);
	
	return APP_INIT_SUCCESS;  //successful
}

//----------------------------------------------------------------------
// RUNTIME


u32 xmhf_hypapp_handlehypercall(context_desc_t context_desc, u64 hypercall_id, u64 hypercall_param){
	u32 status=APP_SUCCESS;
	u32 call_id;
	
	call_id= hypercall_id;

	_XDPRINTF_("\nCPU(%02x): %s starting: call number=%x", context_desc.cpu_desc.cpu_index, __FUNCTION__, call_id);

	switch(call_id){
		case HELLOWORLD_PING:{
			_XDPRINTF_("%s: helloworld ping!");
		}
		break;

		default:
			_XDPRINTF_("\nCPU(0x%02x): unsupported hypercall (0x%08x)!!", 
			  context_desc.cpu_desc.cpu_index, call_id);
			status=APP_ERROR;
			break;
	}

	return status;			
}


//handles XMHF shutdown callback
//note: should not return
void xmhf_hypapp_handleshutdown(context_desc_t context_desc){
	_XDPRINTF_("\n%s:%u: rebooting now", __FUNCTION__, context_desc.cpu_desc.cpu_index);
	XMHF_SLAB_CALL(xc_api_platform_shutdown(context_desc));				
}

//handles h/w pagetable violations
//for now this always returns APP_SUCCESS
u32 xmhf_hypapp_handleintercept_hptfault(context_desc_t context_desc, u64 gpa, u64 gva, u64 error_code){
	u32 status = APP_SUCCESS;

	_XDPRINTF_("\nCPU(%02x): FATAL HWPGTBL violation (gva=%x, gpa=%x, code=%x): unhandled", context_desc.cpu_desc.cpu_index, (u32)gva, (u32)gpa, (u32)error_code);
	HALT();
	
	return status;
}


//handles i/o port intercepts
//returns either APP_IOINTERCEPT_SKIP or APP_IOINTERCEPT_CHAIN
u32 xmhf_hypapp_handleintercept_trap(context_desc_t context_desc, xc_hypapp_arch_param_t xc_hypapp_arch_param){
 	return APP_TRAP_CHAIN;
}

////////
XMHF_SLAB("xhhelloworld")

XMHF_SLAB_DEFINTERFACE(
	XMHF_SLAB_DEFEXPORTFN(xmhf_hypapp_initialization				,XMHF_SLAB_HYPAPP_HYPERDEP_FNINITIALIZATION							,	XMHF_SLAB_FN_RETTYPE_NORMAL)
	XMHF_SLAB_DEFEXPORTFN(xmhf_hypapp_handlehypercall				,XMHF_SLAB_HYPAPP_HYPERDEP_FNHANDLEHYPERCALL						,	XMHF_SLAB_FN_RETTYPE_NORMAL)
	XMHF_SLAB_DEFEXPORTFN(xmhf_hypapp_handleintercept_hptfault		,XMHF_SLAB_HYPAPP_HYPERDEP_FNHANDLEINTERCEPTHPTFAULT				,	XMHF_SLAB_FN_RETTYPE_NORMAL)
	XMHF_SLAB_DEFEXPORTFN(xmhf_hypapp_handleintercept_trap			,XMHF_SLAB_HYPAPP_HYPERDEP_FNHANDLEINTERCEPTTRAP					,	XMHF_SLAB_FN_RETTYPE_NORMAL)
	XMHF_SLAB_DEFEXPORTFN(xmhf_hypapp_handleshutdown				,XMHF_SLAB_HYPAPP_HYPERDEP_FNSHUTDOWN								,	XMHF_SLAB_FN_RETTYPE_NORMAL)
)


