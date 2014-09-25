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

// hyperdep hypapp main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xhhyperdep.h>

#include <xcapi.h>

/////////////////////////////////////////////////////////////////////
slab_retval_t xhhyperdep_interface(u32 src_slabid, u32 dst_slabid, u32 fn_id, u32 fn_paramsize, ...){
	slab_retval_t srval;
	va_list args;

	_XDPRINTF_("%s: Got control: src_slabid=%u, dst_slabid=%u, fn_id=%u, fn_paramsize=%u\n", __FUNCTION__, src_slabid, dst_slabid, fn_id, fn_paramsize);

	switch(fn_id){
			case XMHF_SLAB_HYPAPP_FNINITIALIZATION:{
				context_desc_t context_desc;
				hypapp_env_block_t hypappenvb;
				va_start(args, fn_paramsize);
				context_desc = va_arg(args, context_desc_t);
				hypappenvb = va_arg(args, hypapp_env_block_t);
				srval.retval_u32 = xmhf_hypapp_initialization(context_desc, hypappenvb);
				va_end(args);
			}
			break;

			case XMHF_SLAB_HYPAPP_FNHANDLEHYPERCALL:{
				context_desc_t context_desc;
				u64 hypercall_id;
				u64 hypercall_param;
				va_start(args, fn_paramsize);
				context_desc = va_arg(args, context_desc_t);
				hypercall_id = va_arg(args, u64);
				hypercall_param = va_arg(args, u64);
				srval.retval_u32 = xmhf_hypapp_handlehypercall(context_desc, hypercall_id, hypercall_param);
				va_end(args);
			}
			break;

			case XMHF_SLAB_HYPAPP_FNHANDLEINTERCEPTHPTFAULT:{
				context_desc_t context_desc;
				u64 gpa;
				u64 gva;
				u64 error_code;
				va_start(args, fn_paramsize);
				context_desc = va_arg(args, context_desc_t);
				gpa = va_arg(args, u64);
				gva = va_arg(args, u64);
				error_code = va_arg (args, u64);
				srval.retval_u32 = xmhf_hypapp_handleintercept_hptfault(context_desc, gpa, gva, error_code);
				va_end(args);
			}
			break;

			case XMHF_SLAB_HYPAPP_FNHANDLEINTERCEPTTRAP:{
				context_desc_t context_desc;
				xc_hypapp_arch_param_t xc_hypapp_arch_param;
				va_start(args, fn_paramsize);
				context_desc = va_arg(args, context_desc_t);
				xc_hypapp_arch_param = va_arg(args, xc_hypapp_arch_param_t);
				srval.retval_u32 = xmhf_hypapp_handleintercept_trap(context_desc, xc_hypapp_arch_param);
				va_end(args);
			}
			break;

			case XMHF_SLAB_HYPAPP_FNSHUTDOWN:{
				context_desc_t context_desc;
				va_start(args, fn_paramsize);
				context_desc = va_arg(args, context_desc_t);
				xmhf_hypapp_handleshutdown(context_desc);
				va_end(args);
			}
			break;

			default:
				_XDPRINTF_("%s: unhandled subinterface %u. Halting\n", __FUNCTION__, fn_id);
				HALT();
	}

	return srval;
}

//////////////////////////////////////////////////////////////////////////

#define HYPERDEP_ACTIVATEDEP			0xC0
#define HYPERDEP_DEACTIVATEDEP			0xC1
#define HYPERDEP_INITIALIZE				0xC2

u32 hd_runtimephysbase=0;
u32 hd_runtimesize=0;


// hypapp initialization
u32 xmhf_hypapp_initialization(context_desc_t context_desc, hypapp_env_block_t hypappenvb){
	_XDPRINTF_("CPU %u: hyperDEP initializing\n", context_desc.cpu_desc.cpu_index);

	//store runtime base and size
	hd_runtimephysbase = hypappenvb.runtimephysmembase;
	hd_runtimesize = hypappenvb.runtimesize;

	_XDPRINTF_("%s: XMHF runtime base=%08x, size=%08x\n", __FUNCTION__, hd_runtimephysbase, hd_runtimesize);

	_XDPRINTF_("CPU %u: hyperDEP initialized!\n", context_desc.cpu_desc.cpu_index);

	return APP_INIT_SUCCESS;  //successful
}

//----------------------------------------------------------------------
// RUNTIME

static void hd_activatedep(context_desc_t context_desc, u32 gpa){
	u64 entry;
    slab_retval_t srval;

    srval = XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTGETPROT, XMHF_SLAB_XCAPI_FNXCAPIHPTGETPROT_SIZE, context_desc, gpa);
    _XDPRINTF_("\n%s:%u originalprotection=%08x", __FUNCTION__, context_desc.cpu_desc.cpu_index, srval.retval_u32);
    //_XDPRINTF_("\n%s:%u originalprotection=%08x", __FUNCTION__, context_desc.cpu_desc.cpu_index, XMHF_SLAB_CALL(xc_api_hpt_getprot(context_desc, gpa)) );
	srval = XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTGETENTRY, XMHF_SLAB_XCAPI_FNXCAPIHPTGETENTRY_SIZE, context_desc, (u64)gpa);
    entry = srval.retval_u64;
    XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTSETENTRY, XMHF_SLAB_XCAPI_FNXCAPIHPTSETENTRY_SIZE, context_desc, (u64)gpa, entry);
	XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTSETPROT, XMHF_SLAB_XCAPI_FNXCAPIHPTSETPROT_SIZE, context_desc, (u64)gpa, (u32)(MEMP_PROT_PRESENT | MEMP_PROT_READWRITE | MEMP_PROT_NOEXECUTE));

	//flush hpt caches on CPU
    XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHES, XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHES_SIZE, context_desc);
	//quiesce all CPUs to perform TLB shootdown
    XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPIPLATFORM_INDEX, XMHF_SLAB_XCAPIPLATFORM_FNQUIESCECPUSINPARTITION, XMHF_SLAB_XCAPIPLATFORM_FNQUIESCECPUSINPARTITION_SIZE, context_desc);

	_XDPRINTF_("\nCPU(%02x): %s removed EXECUTE permission for page at gpa %08x", context_desc.cpu_desc.cpu_index, __FUNCTION__, gpa);
}

//de-activate DEP protection
static void hd_deactivatedep(context_desc_t context_desc, u32 gpa){
	XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTSETPROT, XMHF_SLAB_XCAPI_FNXCAPIHPTSETPROT_SIZE, context_desc, (u64)gpa, (u32)(MEMP_PROT_PRESENT | MEMP_PROT_READWRITE | MEMP_PROT_EXECUTE));

	//flush hpt caches on CPU
    XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHES, XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHES_SIZE, context_desc);
	//quiesce all CPUs to perform TLB shootdown
    XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPIPLATFORM_INDEX, XMHF_SLAB_XCAPIPLATFORM_FNQUIESCECPUSINPARTITION, XMHF_SLAB_XCAPIPLATFORM_FNQUIESCECPUSINPARTITION_SIZE, context_desc);


	_XDPRINTF_("\nCPU(%02x): %s added EXECUTE permission for page at gpa %08x", context_desc.cpu_desc.cpu_index, __FUNCTION__, gpa);

}

static void hd_initialize(context_desc_t context_desc){
	_XDPRINTF_("%s: nothing to do\n", __FUNCTION__);
}


u32 xmhf_hypapp_handlehypercall(context_desc_t context_desc, u64 hypercall_id, u64 hypercall_param){
	u32 status=APP_SUCCESS;
	u32 call_id;
	u32 gva, gpa;
    slab_retval_t srval;

	call_id= hypercall_id;

	gva=(u32)hypercall_param;

	_XDPRINTF_("\nCPU(%02x): %s starting: call number=%x, gva=%x", context_desc.cpu_desc.cpu_index, __FUNCTION__, call_id, gva);

	switch(call_id){
		case HYPERDEP_INITIALIZE:{
			hd_initialize(context_desc);
		}
		break;

		case HYPERDEP_ACTIVATEDEP:{
			srval = XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTLVL2PAGEWALK, XMHF_SLAB_XCAPI_FNXCAPIHPTLVL2PAGEWALK_SIZE, context_desc, gva);
			gpa = srval.retval_u32;
			if(gpa == 0xFFFFFFFFUL){
				_XDPRINTF_("CPU(%02x): WARNING: unable to get translation for gva=%x, just returning\n", context_desc.cpu_desc.cpu_index, gva);
				return status;
			}
			_XDPRINTF_("CPU(%02x): translated gva=%x to gpa=%x\n", context_desc.cpu_desc.cpu_index, gva, gpa);
			hd_activatedep(context_desc, gpa);
		}
		break;

		case HYPERDEP_DEACTIVATEDEP:{
			srval = XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTLVL2PAGEWALK, XMHF_SLAB_XCAPI_FNXCAPIHPTLVL2PAGEWALK_SIZE, context_desc, gva);
            gpa = srval.retval_u32;
			if(gpa == 0xFFFFFFFFUL){
				_XDPRINTF_("CPU(%02x): WARNING: unable to get translation for gva=%x, just returning\n", context_desc.cpu_desc.cpu_index, gva);
				return status;
			}
			_XDPRINTF_("CPU(%02x): translated gva=%x to gpa=%x\n", context_desc.cpu_desc.cpu_index, gva, gpa);
			hd_deactivatedep(context_desc, gpa);
		}
		break;

		default:
			_XDPRINTF_("CPU(0x%02x): unsupported hypercall (0x%08x)!!\n",
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
	XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIPLATFORMSHUTDOWN, XMHF_SLAB_XCAPI_FNXCAPIPLATFORMSHUTDOWN_SIZE, context_desc);

}

//handles h/w pagetable violations
//for now this always returns APP_SUCCESS
u32 xmhf_hypapp_handleintercept_hptfault(context_desc_t context_desc, u64 gpa, u64 gva, u64 error_code){
	u32 status = APP_SUCCESS;

	_XDPRINTF_("CPU(%02x): FATAL HWPGTBL violation (gva=%x, gpa=%x, code=%x): app tried to execute data page??\n", context_desc.cpu_desc.cpu_index, (u32)gva, (u32)gpa, (u32)error_code);
	HALT();

	return status;
}


//handles i/o port intercepts
//returns either APP_IOINTERCEPT_SKIP or APP_IOINTERCEPT_CHAIN
u32 xmhf_hypapp_handleintercept_trap(context_desc_t context_desc, xc_hypapp_arch_param_t xc_hypapp_arch_param){
 	return APP_TRAP_CHAIN;
}


//quiesce handler
void xmhf_hypapp_handlequiesce(context_desc_t context_desc){
	//flush hpt caches on CPU
    XMHF_SLAB_CALL_P2P(xcapi, XMHF_SLAB_XHHYPERDEP_INDEX, XMHF_SLAB_XCAPI_INDEX, XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHES, XMHF_SLAB_XCAPI_FNXCAPIHPTFLUSHCACHES_SIZE, context_desc);
}

////////
XMHF_SLAB_DEF(xhhyperdep)


