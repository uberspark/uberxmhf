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
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <xc_ihub.h>
//#include <uapi_gcpustate.h>
//#include <uapi_hcpustate.h>
//#include <xh_hyperdep.h>
//#include <xh_syscalllog.h>
//#include <xh_ssteptrace.h>
//#include <xh_approvexec.h>

/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


//#if 0
/*@
	requires 0 <= hcbentry < HYPAPP_INFO_TABLE_NUMENTRIES;
        requires 0 <= cbtype <= XC_HYPAPPCB_MAXMASK;

	assigns \nothing;
	//behavior yes_hypapp_cb:
	ensures (_xcihub_hypapp_info_table[hcbentry].cbmask & XC_HYPAPPCB_MASK(cbtype)) ==>
		(\result == XC_HYPAPPCB_CHAIN || \result == XC_HYPAPPCB_NOCHAIN);

	//behavior no_hypapp_cb:
	ensures !(_xcihub_hypapp_info_table[hcbentry].cbmask & XC_HYPAPPCB_MASK(cbtype)) ==>
		(\result == XC_HYPAPPCB_CHAIN);

	//complete behaviors;
	//disjoint behaviors;
@*/
static u32 xc_hcbinvoke_helper(u32 hcbentry, u32 cbtype, u32 src_slabid, u32 cpuid, u32 guest_slab_index, u32 cbqual){
	u32 status = XC_HYPAPPCB_CHAIN;
	slab_params_t spl;
	//xc_hypappcb_params_t *hcbp = (xc_hypappcb_params_t *)&spl.in_out_params[0];

	spl.src_slabid = src_slabid;
	spl.cpuid = cpuid;
	spl.dst_uapifn = 0;
	spl.in_out_params[0]=cbtype; //hcbp->cbtype=cbtype;
	spl.in_out_params[1]=cbqual; //hcbp->cbqual=cbqual;
	spl.in_out_params[2]=guest_slab_index; //hcbp->guest_slab_index=guest_slab_index;

        if(_xcihub_hypapp_info_table[hcbentry].cbmask & XC_HYPAPPCB_MASK(cbtype)){
            spl.dst_slabid = _xcihub_hypapp_info_table[hcbentry].xmhfhic_slab_index;
            XMHF_SLAB_CALLNEW(&spl);
            if(spl.in_out_params[3] == XC_HYPAPPCB_NOCHAIN){
		status = XC_HYPAPPCB_NOCHAIN;
            }
	    ////@assert status == XC_HYPAPPCB_CHAIN || status == XC_HYPAPPCB_NOCHAIN;
	    return status;
        }else{
	    ////@assert status == XC_HYPAPPCB_CHAIN;
            return status;
        }

}
//#endif



/*@
	requires 0 <= cbtype <= XC_HYPAPPCB_MAXMASK;
@*/
u32 xc_hcbinvoke(u32 src_slabid, u32 cpuid, u32 cbtype, u32 cbqual, u32 guest_slab_index){
    u32 status = XC_HYPAPPCB_CHAIN;
    u32 i;
	/*@
		loop invariant a1: 0 <= i <= HYPAPP_INFO_TABLE_NUMENTRIES;
		loop assigns i;
		loop assigns status;
		loop variant HYPAPP_INFO_TABLE_NUMENTRIES - i;
	@*/
    for(i=0; i < HYPAPP_INFO_TABLE_NUMENTRIES; i++){
        status = xc_hcbinvoke_helper(i, cbtype, src_slabid, cpuid, guest_slab_index, cbqual);
	if(status == XC_HYPAPPCB_NOCHAIN)
		break;
    }

    return status;
}


