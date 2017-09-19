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
	requires 0 <= saved_state->num_var_mtrrs < MAX_VARIABLE_MTRRS;
	assigns \nothing;
@*/
bool validate_mtrrs(mtrr_state_t *saved_state)
{
	    mtrr_cap_t mtrr_cap;
	    int ndx;

	    // check is meaningless if MTRRs were disabled
	    if ( saved_state->mtrr_def_type.e == 0 )
		return true;

	    // number variable MTRRs
	    unpack_mtrr_cap_t(&mtrr_cap, CASM_FUNCCALL(rdmsr64,MSR_MTRRcap));
	    if ( mtrr_cap.vcnt < saved_state->num_var_mtrrs )
		return false;


	    // variable MTRRs describing non-contiguous memory regions
	    // TBD: assert(MAXPHYADDR == 36);


	/*@
		loop invariant I1: 0 <= ndx <= saved_state->num_var_mtrrs;
		loop assigns ndx;
		loop variant saved_state->num_var_mtrrs - ndx;
	@*/
	for ( ndx = 0; ndx < saved_state->num_var_mtrrs; ndx++ ) {
		uint64_t tb;

		if ( saved_state->mtrr_physmasks[ndx].v == 0 )
		    continue;

		/*@
			loop invariant I2: 0x1 <= tb <= 0x2000000;
			loop assigns tb;
			loop variant 0x1000000 - tb;
		@*/
		for ( tb = 0x1; tb < 0x1000000; tb = tb * 2 ) {
		    if ( (tb & saved_state->mtrr_physmasks[ndx].mask) != 0 )
			break;
		}

		/*@
			loop invariant I2: 0x1 <= tb <= 0x2000000;
			loop assigns tb;
			loop variant 0x1000000 - tb;
		@*/
		for ( ; tb < 0x1000000; tb = tb * 2 ) {
		    if ( (tb & saved_state->mtrr_physmasks[ndx].mask) == 0 )
			break;
		}


		if ( tb != 0x1000000 )
		    return false; // var MTRRs with non-contiguous regions
	}




	// overlaping regions with invalid memory type combinations
	/*@
		loop invariant J1: 0 <= ndx <= saved_state->num_var_mtrrs;
		loop assigns ndx;
		loop variant saved_state->num_var_mtrrs - ndx;
	@*/
	for ( ndx = 0; ndx < saved_state->num_var_mtrrs; ndx++ ) {
		int i;
		const mtrr_physbase_t *base_ndx = &saved_state->mtrr_physbases[ndx];
		const mtrr_physmask_t *mask_ndx = &saved_state->mtrr_physmasks[ndx];

		if ( mask_ndx->v == 0 )
		    continue;

		/*@
			loop invariant J2: ndx+1 <= i <= saved_state->num_var_mtrrs;
			loop assigns i;
			loop variant saved_state->num_var_mtrrs - i;
		@*/
		for ( i = ndx + 1; i < saved_state->num_var_mtrrs; i++ ) {
			int j;
			const mtrr_physbase_t *base_i = &saved_state->mtrr_physbases[i];
			const mtrr_physmask_t *mask_i = &saved_state->mtrr_physmasks[i];

			if ( mask_i->v == 0 )
				continue;

			if ( (base_ndx->base & mask_ndx->mask & mask_i->mask)
			    != (base_i->base & mask_i->mask)
			 && (base_i->base & mask_i->mask & mask_ndx->mask)
			    != (base_ndx->base & mask_ndx->mask) )
				continue;

			if ( base_ndx->type == base_i->type )
				continue;
			if ( base_ndx->type == MTRR_TYPE_UNCACHABLE
			 || base_i->type == MTRR_TYPE_UNCACHABLE )
				continue;
			if ( base_ndx->type == MTRR_TYPE_WRTHROUGH
			 && base_i->type == MTRR_TYPE_WRBACK )
				continue;
			if ( base_ndx->type == MTRR_TYPE_WRBACK
			 && base_i->type == MTRR_TYPE_WRTHROUGH )
				continue;


			/* 2 overlapped regions have invalid mem type combination, */
			/* need to check whether there is a third region which has type */
			/* of UNCACHABLE and contains at least one of these two regions. */
			/* If there is, then the combination of these 3 region is valid */
			/*@
				loop invariant J3: 0 <= j <= saved_state->num_var_mtrrs;
				loop assigns j;
				loop variant saved_state->num_var_mtrrs - j;
			@*/

			for ( j = 0; j < saved_state->num_var_mtrrs; j++ ) {
				const mtrr_physbase_t *base_j
					= &saved_state->mtrr_physbases[j];
				const mtrr_physmask_t *mask_j
					= &saved_state->mtrr_physmasks[j];

				if ( mask_j->v == 0 )
				    continue;

				if ( base_j->type != MTRR_TYPE_UNCACHABLE )
				    continue;

				if ( (base_ndx->base & mask_ndx->mask & mask_j->mask)
					== (base_j->base & mask_j->mask)
				     && (mask_j->mask & ~mask_ndx->mask) == 0 )
				    break;

				if ( (base_i->base & mask_i->mask & mask_j->mask)
					== (base_j->base & mask_j->mask)
				     && (mask_j->mask & ~mask_i->mask) == 0 )
				    break;
			}

			if ( j < saved_state->num_var_mtrrs )
				continue;

			return false; //var MTRRs overlaping regions, invalid type combinations
		}

	}


	return true;
}
