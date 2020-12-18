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
 * vft slab stubs verification driver
 * author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark.h>
#include <xmhfgeec.h>

uint32_t cpuid = 0;	//BSP cpu
slab_params_t sp;

/*
__CALL_FROM_VfT_PROG__
__CALL_uVT_uVU_PROG_TO_VfT_PROG__
__CALL_EXCEPTION__
__CALL_INTERCEPT__
*/

#if defined (__CALL_FROM_VfT_PROG__)
void xmhfhwm_vdriver_sentinel(void){
	//@assert 0;
}
#endif //__CALL_FROM_VfT_PROG__

#if defined (__CALL_uVT_uVU_PROG_TO_VfT_PROG__)
void xmhfhwm_vdriver_sentinel(void){
	//@assert sp.slab_ctype == XMHFGEEC_SENTINEL_RET_uVT_uVU_PROG_TO_VfT_PROG;
	//@assert sp.src_slabid == 6;
	//@assert sp.dst_slabid == 5;
	//@assert 0;
}
#endif //__CALL_uVT_uVU_PROG_TO_VfT_PROG__

#if defined (__CALL_EXCEPTION__)
void xmhfhwm_vdriver_sentinel(void){
	//@assert sp.slab_ctype == XMHFGEEC_SENTINEL_RET_EXCEPTION;
	//@assert sp.src_slabid == 6;
	//@assert sp.dst_slabid == 5;
	//@assert 0;
}
#endif //__CALL_EXCEPTION__

#if defined (__CALL_INTERCEPT__)
void xmhfhwm_vdriver_sentinel(void){
	//@assert sp.slab_ctype == XMHFGEEC_SENTINEL_RET_INTERCEPT;
	//@assert sp.src_slabid == 6;
	//@assert sp.dst_slabid == 5;
	//@assert 0;
}
#endif //__CALL_INTERCEPT__


void slab_main(slab_params_t *sp){
	// //@assert sp->slab_ctype == 0xFF;

}


void main(void){
	uint32_t *stackelem;
	uint32_t check_esp, check_eip = CASM_RET_EIP;
	uint64_t val;


	//initialize sp
#if defined (__CALL_FROM_VfT_PROG__)
	sp.slab_ctype = XMHFGEEC_SENTINEL_CALL_FROM_VfT_PROG;
#endif //__CALL_FROM_VfT_PROG__
#if defined (__CALL_uVT_uVU_PROG_TO_VfT_PROG__)
	sp.slab_ctype = XMHFGEEC_SENTINEL_CALL_uVT_uVU_PROG_TO_VfT_PROG;
#endif //__CALL_uVT_uVU_PROG_TO_VfT_PROG__
#if defined (__CALL_EXCEPTION__)
	sp.slab_ctype = XMHFGEEC_SENTINEL_CALL_EXCEPTION;
#endif //__CALL_EXCEPTION__
#if defined (__CALL_INTERCEPT__)
	sp.slab_ctype = XMHFGEEC_SENTINEL_CALL_INTERCEPT;
#endif //__CALL_INTERCEPT__

	sp.src_slabid = 5;
	sp.dst_slabid = 6;
	sp.dst_uapifn = 0;
	sp.cpuid = cpuid;

	//populate hardware model stack
	xmhfhwm_cpu_gprs_esp = _slab_tos[cpuid];
	check_esp = xmhfhwm_cpu_gprs_esp - sizeof(uint32_t); // pointing to sp

	// upon control transfer to a slab entry stub the stack is
	// setup by the sentinel as follows:
	// TOS: <return eip>, slab_params_t *
	// simulate this by using CASM_FUNCCALL on _slab_entrystub with
	// sp as the sole parameter
	val = CASM_FUNCCALL(_slab_entrystub, (void *)&sp);

#if defined (__CALL_FROM_VfT_PROG__)
	//@assert xmhfhwm_cpu_gprs_esp == check_esp;
	//@assert xmhfhwm_cpu_gprs_eip == check_eip;
#endif //__CALL_FROM_VfT_PROG__


}


