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

//Intel VT-d declarations/definitions
//author: amit vasudevan (amitvasudevan@acm.org)

#include <uberspark.h>
#include <xmhfhw.h>


//VT-d translation has 1 root entry table (RET) of 4kb
//each root entry (RE) is 128-bits which gives us 256 entries in the
//RET, each corresponding to a PCI bus num. (0-255)
//each RE points to a context entry table (CET) of 4kb
//each context entry (CE) is 128-bits which gives us 256 entries in
//the CET, accounting for 32 devices with 8 functions each as per the
//PCI spec.
//each CE points to a PDPT type paging structure for  device
/*@
	requires \valid(drhd);
	assigns \nothing;
@*/
bool xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(VTD_DRHD *drhd,  uint64_t ret_addr){
	VTD_RTADDR_REG rtaddr;
	VTD_GCMD_REG gcmd;
	VTD_GSTS_REG gsts;
	uint32_t retbuffer_paddr = (uint32_t)ret_addr;

	//sanity check
	if (drhd == NULL)
		return false;

	//setup DRHD RET (root-entry)
	unpack_VTD_RTADDR_REG(&rtaddr, retbuffer_paddr);
	_vtd_reg_write(drhd, VTD_RTADDR_REG_OFF, pack_VTD_RTADDR_REG(&rtaddr));

	//latch RET address by using GCMD.SRTP
	unpack_VTD_GCMD_REG(&gcmd, 0);
	gcmd.srtp=1;
	_vtd_reg_write(drhd, VTD_GCMD_REG_OFF, pack_VTD_GCMD_REG(&gcmd));

	//ensure the RET address was latched by the h/w
        unpack_VTD_GSTS_REG(&gsts, _vtd_reg_read(drhd, VTD_GSTS_REG_OFF));

	if(!gsts.rtps){
		//_XDPRINTF_("Error	Failed to latch RTADDR\n");
		return false;
	}

	return true;
}


