/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
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

//Intel VT-d declarations/definitions
//author: amit vasudevan (amitvasudevan@acm.org)

#include <uberspark.h>
#include <xmhfhw.h>


//initialize a given DRHD unit to meet our requirements
/*@
	requires \valid(drhd);
	assigns \nothing;
@*/
bool xmhfhw_platform_x86pc_vtd_drhd_initialize(VTD_DRHD *drhd){
	VTD_GCMD_REG gcmd;
	VTD_GSTS_REG gsts;
	VTD_FECTL_REG fectl;
	VTD_CAP_REG cap;

	//sanity check
	if (drhd == NULL)
		return false;


	//read CAP register
	unpack_VTD_CAP_REG(&cap, _vtd_reg_read(drhd, VTD_CAP_REG_OFF));

	if(! (cap.plmr && cap.phmr) ){
		//_XDPRINTF_("\n%s: Error: PLMR unsupported", __func__);
		return false;
	}

        if ( !((cap.sagaw & 0x2) || (cap.sagaw & 0x4)) ){
		//_XDPRINTF_("%s: Error: we only support 3-level or 4-level tables (%x)\n", __func__, cap.bits.sagaw);
		return false;
        }


	//setup fault logging
	//read FECTL
	unpack_VTD_FECTL_REG(&fectl, _vtd_reg_read(drhd, VTD_FECTL_REG_OFF));

	//set interrupt mask bit and write
	fectl.im=1;
	_vtd_reg_write(drhd, VTD_FECTL_REG_OFF, pack_VTD_FECTL_REG(&fectl) );

	//check to see if the IM bit actually stuck
	unpack_VTD_FECTL_REG(&fectl, _vtd_reg_read(drhd, VTD_FECTL_REG_OFF));

	if(!fectl.im){
		//_XDPRINTF_("\n%s: Error: Failed to set fault-reporting.", __func__);
		return false;
	}

	return true;
}


