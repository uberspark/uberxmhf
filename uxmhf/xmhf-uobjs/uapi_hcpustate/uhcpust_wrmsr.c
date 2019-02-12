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

/*
 * host CPU state uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>
#include <xmhfgeec.h>

#include <uapi_hcpustate.h>


//@ghost bool uhcpust_wrmsr_callwrmsr = false;
/*@
	requires \valid(msrp);
	requires 0 <= srcslabid < XMHFGEEC_TOTAL_SLABS;

	behavior fromprime:
		assumes (srcslabid == XMHFGEEC_SLAB_GEEC_PRIME);
		ensures (uhcpust_wrmsr_callwrmsr == true);

	behavior notfromprime_valid:
		assumes !(srcslabid == XMHFGEEC_SLAB_GEEC_PRIME);
		assumes (msrp->msr != MSR_EFER);
		ensures (uhcpust_wrmsr_callwrmsr == true);

	behavior notfromprime_invalid:
		assumes !(srcslabid == XMHFGEEC_SLAB_GEEC_PRIME);
		assumes (msrp->msr == MSR_EFER);
		ensures (uhcpust_wrmsr_callwrmsr == false);

	complete behaviors;
	disjoint behaviors;
@*/
void uhcpust_wrmsr(uint32_t srcslabid, xmhf_uapi_hcpustate_msr_params_t *msrp){
	if(srcslabid == XMHFGEEC_SLAB_GEEC_PRIME){
		CASM_FUNCCALL(wrmsr64, msrp->msr, (uint32_t)msrp->value, (uint32_t)((uint64_t)msrp->value >> 32) );
		//@ghost uhcpust_wrmsr_callwrmsr = true;
	}else{
		if(msrp->msr != MSR_EFER){
			CASM_FUNCCALL(wrmsr64, msrp->msr, (uint32_t)msrp->value, (uint32_t)((uint64_t)msrp->value >> 32) );
			//@ghost uhcpust_wrmsr_callwrmsr = true;
		}else{
			//invalid write
			//@ghost uhcpust_wrmsr_callwrmsr = false;
		}
	}
}
