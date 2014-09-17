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
 * XMHF core device initialization slab (xcdev), x86-vmx-x86pc arch. backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcdev.h>

bool xcdev_arch_initialize(void){

	vtd_drhd_handle_t drhd_handle;
	u32 vtd_dmar_table_physical_address=0;
	vtd_drhd_handle_t vtd_drhd_maxhandle;

	//scan for available DRHD units in the platform
	if(!xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(&vtd_drhd_maxhandle, &vtd_dmar_table_physical_address)){
        _XDPRINTF_("%s: unable to scan for DRHD units. bailing out!\n", __FUNCTION__);
		return false;
	}

    _XDPRINTF_("%s: maxhandle = %u, dmar table addr=0x%08x\n", __FUNCTION__,
                (u32)vtd_drhd_maxhandle, (u32)vtd_dmar_table_physical_address);


	//initialize all DRHD units
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
   		//VTD_CAP_REG cap;
		//VTD_ECAP_REG ecap;

		_XDPRINTF_("%s: Setting up DRHD unit %u...\n", __FUNCTION__, drhd_handle);

		if(!xmhfhw_platform_x86pc_vtd_drhd_initialize(drhd_handle) ){
            _XDPRINTF_("%s: error setting up DRHD unit %u. bailing out!\n", __FUNCTION__, drhd_handle);
			return false;
		}

        //cap.value = xmhfhw_platform_x86pc_vtd_drhd_reg_read(drhd_handle, VTD_CAP_REG_OFF);
        //ecap.value = xmhfhw_platform_x86pc_vtd_drhd_reg_read(drhd_handle, VTD_ECAP_REG_OFF);

        //_XDPRINTF_(" cap.bits.sps=%x, cap.bits.sagaw=%x, ecap=%016llx\n", cap.bits.sps, cap.bits.sagaw, ecap.value);
	}

    return true;
}
