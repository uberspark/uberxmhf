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
 GEEC sentinel low-level support routines
 author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhf-debug.h>
#include <xmhfgeec.h>
#include <geec_sentinel.h>

//////
// sentinel [p_call] entry point
//////


// C invocation of this function is of type _slab_entrystub(slab_params_t *sp)
// Pre: [esp] = return address to resume the (verified,privileged) caller
//	[esp+4] = slab_params_t *sp (pointer to slab_params_t within caller
//					memory area)

CASM_FUNCDEF_FULL(.slab_entrystub, 1, void, _slab_entrystub,
{
	xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
	xmhfhwm_cpu_insn_pushl_ebp();
	xmhfhwm_cpu_insn_pushl_edi();
	xmhfhwm_cpu_insn_pushl_esi();
	xmhfhwm_cpu_insn_pushl_ebx();
	xmhfhwm_cpu_insn_movl_esp_edx();
	xmhfhwm_cpu_insn_pushl_edx();
	xmhfhwm_cpu_insn_pushl_eax();
	// Post:
	//  	[esp] = slab_params_t *sp
	//	[esp+4] = &[esp+8]
	//	[esp+8] = ebx
	//	[esp+12] = esi
	//	[esp+16] = edi
	//	[esp+20] = ebp
	//	[esp+24] = return address to resume the (verified,privileged) caller
	//	[esp+28] = slab_params_t *sp
	xmhfhwm_cpu_insn_call(geec_sentinel_main);

	// Pre: false; should never get here when verifying this CASM
	// function. if we do end up here the following hlt will trigger
	// verification error
	xmhfhwm_cpu_insn_hlt();
	// Post: false; should never get here
},
slab_params_t *sp)

