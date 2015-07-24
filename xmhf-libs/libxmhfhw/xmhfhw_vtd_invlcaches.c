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

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfhw.h>
#include <xmhf-debug.h>



//invalidate DRHD caches
//note: we do global invalidation currently
//returns: true if all went well, else false
bool xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(VTD_DRHD *drhd){
	VTD_CCMD_REG ccmd;
	VTD_IOTLB_REG iotlb;
	//VTD_DRHD *drhd = _vtd_get_drhd_struct(drhd_handle);

	//sanity check
	if (drhd == NULL)
		return false;

	//invalidate CET cache
  	//wait for context cache invalidation request to send
    do{
      //ccmd.value = _vtd_reg_read(drhd, VTD_CCMD_REG_OFF);
      unpack_VTD_CCMD_REG(&ccmd, _vtd_reg_read(drhd, VTD_CCMD_REG_OFF));
    }while(ccmd.icc);

	//initialize CCMD to perform a global invalidation
    //ccmd.value=0;
    memset(&ccmd, 0, sizeof(VTD_CCMD_REG));
    ccmd.cirg=1; //global invalidation
    ccmd.icc=1;  //invalidate context cache

    //perform the invalidation
    _vtd_reg_write(drhd, VTD_CCMD_REG_OFF, pack_VTD_CCMD_REG(&ccmd));

	//wait for context cache invalidation completion status
    do{
      //ccmd.value = _vtd_reg_read(drhd, VTD_CCMD_REG_OFF);
      unpack_VTD_CCMD_REG(&ccmd, _vtd_reg_read(drhd, VTD_CCMD_REG_OFF));
    }while(ccmd.icc);

	//if all went well CCMD CAIG = CCMD CIRG (i.e., actual = requested invalidation granularity)
	if(ccmd.caig != 0x1){
		//_XDPRINTF_("\n%s: Error: Invalidatation of CET failed (%u)", __func__, ccmd.bits.caig);
		return false;
	}

	//invalidate IOTLB
    //initialize IOTLB to perform a global invalidation
	//iotlb.value=0;
	memset(&iotlb, 0, sizeof(VTD_IOTLB_REG));
    iotlb.iirg=1; //global invalidation
    iotlb.ivt=1;	 //invalidate

    //perform the invalidation
	_vtd_reg_write(drhd, VTD_IOTLB_REG_OFF, pack_VTD_IOTLB_REG(&iotlb));

    //wait for the invalidation to complete
    do{
      //iotlb.value = _vtd_reg_read(drhd, VTD_IOTLB_REG_OFF);
      unpack_VTD_IOTLB_REG(&iotlb, _vtd_reg_read(drhd, VTD_IOTLB_REG_OFF));
    }while(iotlb.ivt);

    //if all went well IOTLB IAIG = IOTLB IIRG (i.e., actual = requested invalidation granularity)
	if(iotlb.iaig != 0x1){
		//_XDPRINTF_("\n%s: Error: Invalidation of IOTLB failed (%u)", __func__, iotlb.bits.iaig);
		return false;
    }

	return true;
}


