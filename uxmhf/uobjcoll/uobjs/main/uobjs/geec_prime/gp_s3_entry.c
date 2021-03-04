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

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/uobjs/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/uobjs/main/include/uobjs/geec_prime.h>

//@ghost bool gp_s3_entry_invoked_writecr3 = false;
//@ghost bool gp_s3_entry_invoked_savemtrrs = false;
//@ghost bool gp_s3_entry_invoked_restoremtrrs = false;
//@ghost bool gp_s3_entry_invoked_startcores = false;
//@ghost bool gp_s3_entry_invoked_gp_s5_entry = false;
/*@
	requires 0 <= sinit2mle_mtrrs.num_var_mtrrs < MAX_VARIABLE_MTRRS;
	ensures gp_s3_entry_invoked_writecr3 == true;
	ensures gp_s3_entry_invoked_savemtrrs == true;
	ensures gp_s3_entry_invoked_restoremtrrs == true;
	ensures gp_s3_entry_invoked_startcores == true;
	ensures gp_s3_entry_invoked_gp_s5_entry == true;
@*/
void gp_s3_entry(void){

#if 1
	_XDPRINTF_("%s: proceeding to switch page-tables...\n", __func__);
#endif

	//switch to verified object page tables
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__write_cr3,(uint32_t)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
	//@ghost gp_s3_entry_invoked_writecr3 = true;

	//save cpu MTRR state which we will later replicate on all APs
	//@assert gp_s3_entry_invoked_writecr3 == true;
	uberspark_uobjrtl_hw__generic_x86_32_intel__save_mtrrs(&_mtrrs);
	//@ghost gp_s3_entry_invoked_savemtrrs = true;

	//restore SINIT to MLE MTRR mappings
	//@assert gp_s3_entry_invoked_writecr3 == true;
	//@assert gp_s3_entry_invoked_savemtrrs == true;
	uberspark_uobjrtl_hw__generic_x86_32_intel__restore_mtrrs(&sinit2mle_mtrrs);
	//@ghost gp_s3_entry_invoked_restoremtrrs = true;

	//start all cores
	//@assert gp_s3_entry_invoked_writecr3 == true;
	//@assert gp_s3_entry_invoked_savemtrrs == true;
	//@assert gp_s3_entry_invoked_restoremtrrs == true;
	gp_s3_startcores();
	//@ghost gp_s3_entry_invoked_startcores = true;

	//move on to state-5
	//@assert gp_s3_entry_invoked_writecr3 == true;
	//@assert gp_s3_entry_invoked_savemtrrs == true;
	//@assert gp_s3_entry_invoked_restoremtrrs == true;
	//@assert gp_s3_entry_invoked_startcores == true;
	gp_s5_entry();
	//@ghost gp_s3_entry_invoked_gp_s5_entry = true;

}










