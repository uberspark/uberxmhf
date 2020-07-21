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
#include <uberspark/include/uberspark.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_ihub.h>

/*
 * xc_ihub hypapp callback invocation
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


/*@
	requires 0 <= hcbentry < HYPAPP_INFO_TABLE_NUMENTRIES;
        requires 0 <= cbtype <= XC_HYPAPPCB_MAXMASK;

	assigns \nothing;

	behavior yes_hypapp_cb:
		assumes (_xcihub_hypapp_info_table[hcbentry].cbmask & XC_HYPAPPCB_MASK(cbtype));
		ensures (\result == XC_HYPAPPCB_CHAIN || \result == XC_HYPAPPCB_NOCHAIN);

	behavior no_hypapp_cb:
		assumes !(_xcihub_hypapp_info_table[hcbentry].cbmask & XC_HYPAPPCB_MASK(cbtype));
		ensures (\result == XC_HYPAPPCB_CHAIN);

	complete behaviors;
	disjoint behaviors;
@*/
static uint32_t xc_hcbinvoke_helper(uint32_t hcbentry, uint32_t cbtype, uint32_t src_slabid, uint32_t cpuid, uint32_t guest_slab_index, uint32_t cbqual){
	uint32_t status = XC_HYPAPPCB_CHAIN;
	slab_params_t spl;

	spl.src_slabid = src_slabid;
	spl.cpuid = cpuid;
	spl.dst_uapifn = 0;
	spl.in_out_params[0]=cbtype; //hcbp->cbtype=cbtype;
	spl.in_out_params[1]=cbqual; //hcbp->cbqual=cbqual;
	spl.in_out_params[2]=guest_slab_index; //hcbp->guest_slab_index=guest_slab_index;
	spl.in_out_params[3]=0;

	if(_xcihub_hypapp_info_table[hcbentry].cbmask & XC_HYPAPPCB_MASK(cbtype)){
		spl.dst_slabid = _xcihub_hypapp_info_table[hcbentry].xmhfhic_slab_index;
		XMHF_SLAB_CALLNEW(&spl);
		if(spl.in_out_params[3] == XC_HYPAPPCB_NOCHAIN){
			status = XC_HYPAPPCB_NOCHAIN;
		}
		return status;
	}else{
            return status;
	}
}


//@ghost bool invoke_helper[HYPAPP_INFO_TABLE_NUMENTRIES];
/*@
	requires 0 <= cbtype <= XC_HYPAPPCB_MAXMASK;
	assigns invoke_helper[0..(HYPAPP_INFO_TABLE_NUMENTRIES-1)];
	ensures \result == XC_HYPAPPCB_CHAIN || \result == XC_HYPAPPCB_NOCHAIN;
@*/
uint32_t xc_hcbinvoke(uint32_t src_slabid, uint32_t cpuid, uint32_t cbtype, uint32_t cbqual, uint32_t guest_slab_index){
    uint32_t status = XC_HYPAPPCB_CHAIN;
    bool nochain = false;
    uint32_t i;
	/*@
		loop invariant a1: 0 <= i <= HYPAPP_INFO_TABLE_NUMENTRIES;
		loop invariant a2: \forall integer x; 0 <= x < i ==> ( invoke_helper[x] == true );
		loop assigns i;
		loop assigns status;
		loop assigns nochain;
		loop assigns invoke_helper[0..(HYPAPP_INFO_TABLE_NUMENTRIES-1)];
		loop variant HYPAPP_INFO_TABLE_NUMENTRIES - i;
	@*/
    for(i=0; i < HYPAPP_INFO_TABLE_NUMENTRIES; i++){
        status = xc_hcbinvoke_helper(i, cbtype, src_slabid, cpuid, guest_slab_index, cbqual);
		//@ghost invoke_helper[i] = true;
		if(status == XC_HYPAPPCB_NOCHAIN){
			nochain = true;
			break;
		}
    }

	if(nochain)
		return XC_HYPAPPCB_NOCHAIN;
	else
		return XC_HYPAPPCB_CHAIN;
}


