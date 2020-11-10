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

// aprvexec hypapp main module
// author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhfgeec.h>
#include <xmhf-debug.h>
#include <xc.h>
#include <uapi_gcpustate.h>
#include <uapi_slabmempgtbl.h>
#include <xh_uhcalltest.h>


typedef struct {
  uint8_t in[16];
  uint8_t out[16];
}uhcalltest_param_t;

//////
// hypapp callbacks


//initialization
static void _hcb_initialize(uint32_t cpuindex){
	_XDPRINTF_("%s[%u]: uhcalltest initializing...\n", __func__, (uint16_t)cpuindex);
}

//hypercall
static void _hcb_hypercall(uint64_t cpuindex, uint64_t guest_slab_index){
    slab_params_t spl;
    xmhf_uapi_gcpustate_gprs_params_t *gcpustate_gprs =
        (xmhf_uapi_gcpustate_gprs_params_t *)spl.in_out_params;
    x86regs_t *gprs = (x86regs_t *)&gcpustate_gprs->gprs;
    uint32_t call_id;
    uint64_t gpa;

    spl.src_slabid = XMHFGEEC_SLAB_XH_UHCALLTEST;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;
    spl.cpuid = cpuindex;
    //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;

     spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD;
    XMHF_SLAB_CALLNEW(&spl);


    call_id = gprs->eax;
    gpa = ((uint64_t)gprs->ebx << 32) | gprs->edx;

    switch(call_id){
    case UAPP_UHCALLTEST_FUNCTION_TEST:{
      _XDPRINTF_("%s[%u]: call_id=%x(FUNCTION_TEST), eax=%08x,ebx=%08x,edx=%08x\n",
		 __func__, (uint16_t)cpuindex, call_id, gprs->eax, gprs->ebx, gprs->edx);
      _XDPRINTF_("%s[%u]: call_id=%x(FUNCTION_TEST), gpa=%016llx\n", __func__, (uint16_t)cpuindex, call_id, gpa);

      uhcalltest_param_t *uhctp;
      uhctp = (uhcalltest_param_t *) gpa;
      memcpy(uhctp->out, uhctp->in, 16);
    }
      break;

    default:
      //_XDPRINTF_("%s[%u]: unsupported hypercall %x. Ignoring\n", __func__, (uint16_t)cpuindex, call_id);
      break;
    }

}


// shutdown
static void _hcb_shutdown(uint32_t cpuindex, uint32_t guest_slab_index){
  _XDPRINTF_("%s[%u]: guest slab %u shutdown...\n", __func__, (uint16_t)cpuindex, guest_slab_index);
}



//////
// slab interface
void slab_main(slab_params_t *sp){
  xc_hypappcb_params_t *hcbp = (xc_hypappcb_params_t *)&sp->in_out_params[0];
  hcbp->cbresult=XC_HYPAPPCB_CHAIN;

  switch(hcbp->cbtype){
  case XC_HYPAPPCB_INITIALIZE:{
    _hcb_initialize(sp->cpuid);
  }
    break;

  case XC_HYPAPPCB_HYPERCALL:{
    _hcb_hypercall(sp->cpuid, hcbp->guest_slab_index);
  }
    break;

  case XC_HYPAPPCB_SHUTDOWN:{
    _hcb_shutdown(sp->cpuid, hcbp->guest_slab_index);
  }
    break;

  default:{
    //_XDPRINTF_("%s[%u]: Unknown cbtype. Ignoring!\n",
    //    __func__, (uint16_t)sp->cpuid);
  }
  }

}
