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

//author: amit vasudevan (amitvasudevan@acm.org)

#include <uberspark.h>
#include <xmhfhw.h>

/*@
	requires \valid(saved_state);
	assigns saved_state->mtrr_def_type;
	assigns saved_state->num_var_mtrrs;
	assigns saved_state->mtrr_physbases[0 .. MAX_VARIABLE_MTRRS-1];
	assigns saved_state->mtrr_physmasks[0 .. MAX_VARIABLE_MTRRS-1];
@*/
void xmhfhw_cpu_x86_save_mtrrs(mtrr_state_t *saved_state)
{
	mtrr_cap_t mtrr_cap;
	int ndx;

	// IA32_MTRR_DEF_TYPE MSR
	unpack_mtrr_def_type_t(&saved_state->mtrr_def_type, CASM_FUNCCALL(rdmsr64,MSR_MTRRdefType));

	// sanitize saved_state->num_var_mtrrs
	unpack_mtrr_cap_t(&mtrr_cap, CASM_FUNCCALL(rdmsr64,MSR_MTRRcap));
	if ( mtrr_cap.vcnt > MAX_VARIABLE_MTRRS )
		saved_state->num_var_mtrrs = MAX_VARIABLE_MTRRS;
	else
		saved_state->num_var_mtrrs = mtrr_cap.vcnt;

	//@assert 0 <= saved_state->num_var_mtrrs <= MAX_VARIABLE_MTRRS;

	// save physmask's and physbase's
    	/*@
		loop invariant I1: 0 <= ndx <= saved_state->num_var_mtrrs;
		loop assigns ndx, saved_state->mtrr_physbases[0 .. MAX_VARIABLE_MTRRS-1],saved_state->mtrr_physmasks[0 .. MAX_VARIABLE_MTRRS-1];
		loop variant saved_state->num_var_mtrrs - ndx;
	@*/
	for ( ndx = 0; ndx < saved_state->num_var_mtrrs; ndx++ ) {
		unpack_mtrr_physmask_t(&saved_state->mtrr_physmasks[ndx],
			CASM_FUNCCALL(rdmsr64,MTRR_PHYS_MASK0_MSR + ndx*2));
		unpack_mtrr_physbase_t(&saved_state->mtrr_physbases[ndx],
			CASM_FUNCCALL(rdmsr64,MTRR_PHYS_BASE0_MSR + ndx*2));
	}
}


