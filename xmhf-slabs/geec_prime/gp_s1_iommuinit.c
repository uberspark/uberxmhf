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

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <geec_prime.h>
#include <geec_sentinel.h>
#include <uapi_slabmempgtbl.h>
#include <xc_init.h>




void gp_s1_iommuinit(void){
	vtd_drhd_handle_t drhd_handle;
	vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
	//u32 i, b, d, f;

	vtd_pagewalk_level = VTD_PAGEWALK_NONE;

	//initialize all DRHD units
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
		VTD_CAP_REG cap;

		_XDPRINTF_("%s: Setting up DRHD unit %u...\n", __func__, drhd_handle);


		if(!xmhfhw_platform_x86pc_vtd_drhd_initialize(&vtd_drhd[drhd_handle]) ){
			_XDPRINTF_("%s: error setting up DRHD unit %u. halting!\n", __func__, drhd_handle);
			CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		}

		//@assert 1;

		//read and store DRHD supported page-walk length
		unpack_VTD_CAP_REG(&cap, _vtd_reg_read(&vtd_drhd[drhd_handle], VTD_CAP_REG_OFF));
		if(cap.sagaw & 0x2){
		    if(vtd_pagewalk_level == VTD_PAGEWALK_NONE || vtd_pagewalk_level == VTD_PAGEWALK_3LEVEL){
			vtd_pagewalk_level = VTD_PAGEWALK_3LEVEL;
			_XDPRINTF_("%s: DRHD unit %u - 3-level page-walk\n", __func__, drhd_handle);
		    }else{
			_XDPRINTF_("%s: Halting: mixed hardware supported page-walk lengths\n",
				    __func__);
			CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		    }
		}

		//@assert 1;


		if(cap.sagaw & 0x4){
		    if(vtd_pagewalk_level == VTD_PAGEWALK_NONE || vtd_pagewalk_level == VTD_PAGEWALK_4LEVEL){
			vtd_pagewalk_level = VTD_PAGEWALK_4LEVEL;
			_XDPRINTF_("%s: DRHD unit %u - 4-level page-walk\n", __func__, drhd_handle);
		    }else{
			_XDPRINTF_("%s: Halting: mixed hardware supported page-walk lengths\n",
				    __func__);
			CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		    }
		}

		//@assert 1;


		//set DRHD root entry table
		if(!xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(&vtd_drhd[drhd_handle], vtd_ret_address)){
			_XDPRINTF_("%s: Halting: error in setting DRHD RET\n", __func__);
			CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		}

		//@assert 1;

		#if 0

		//invalidate caches
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(&vtd_drhd[drhd_handle])){
			_XDPRINTF_("%s: Halting: error in invalidating caches\n", __func__);
			CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		}

		//enable VT-d translation
		xmhfhw_platform_x86pc_vtd_drhd_enable_translation(&vtd_drhd[drhd_handle]);

		//disable PMRs now (since DMA protection is active via translation)
		xmhfhw_platform_x86pc_vtd_drhd_disable_pmr(&vtd_drhd[drhd_handle]);
		#endif // 0

		_XDPRINTF_("%s: Successfully setup DRHD unit %u\n", __func__, drhd_handle);
	}

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu32, vtd_dmar_table_physical_address, 0UL);


	_XDPRINTF_("%s: final page-walk level=%u\n", __func__, vtd_pagewalk_level);
}
