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
#include <uberspark/include/uberspark.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
uint32_t check_esp, check_eip = CASM_RET_EIP;

void xmhfhwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
	//@assert (newval >= ((uint32_t)&_init_bsp_cpustack + 4)) && (newval <= ((uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
}

void main(void){
	//populate hardware model stack and program counter
	xmhfhwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
	xmhfhwm_cpu_gprs_eip = check_eip;
	check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack

	//execute harness
	vtd_drhd_maxhandle = 2;
	vtd_drhd_scanned = true;
	vtd_dmar_table_physical_address =XMHFHWM_BIOS_VTDDMARTABLEBASE;
	vtd_ret_address = 0xDEADB000;
	vtd_drhd[0].regbaseaddr =0x00000000fed90000ULL;
	vtd_drhd[0].iotlb_regaddr = 0x00000000fed90108ULL;
	vtd_drhd[0].iva_regaddr = 0x00000000fed90100ULL;
	vtd_drhd[1].regbaseaddr =0x00000000fed91000ULL;
	vtd_drhd[1].iotlb_regaddr = 0x00000000fed91108ULL;
	vtd_drhd[1].iva_regaddr = 0x00000000fed91100ULL;
	gp_s1_iommuinit();
	//@assert xmhfhwm_vtd_drhd_state[0].reg_rtaddr_lo == vtd_ret_address;
	//@assert xmhfhwm_vtd_drhd_state[0].reg_rtaddr_hi == 0;
	//@assert xmhfhwm_vtd_drhd_state[1].reg_rtaddr_lo == vtd_ret_address;
	//@assert xmhfhwm_vtd_drhd_state[1].reg_rtaddr_hi == 0;

	//@assert xmhfhwm_cpu_gprs_esp == check_esp;
	//@assert xmhfhwm_cpu_gprs_eip == check_eip;
}
#endif

void gp_s1_iommuinit(void){
	vtd_drhd_handle_t drhd_handle;
	vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
	//uint32_t i, b, d, f;

	vtd_pagewalk_level = VTD_PAGEWALK_NONE;

	//initialize all DRHD units
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
		VTD_CAP_REG cap;

		_XDPRINTF_("%s: Setting up DRHD unit %u...\n", __func__, drhd_handle);


		if(!xmhfhw_platform_x86pc_vtd_drhd_initialize(&vtd_drhd[drhd_handle]) ){
			_XDPRINTF_("%s: error setting up DRHD unit %u. halting!\n", __func__, drhd_handle);
			CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		}


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

		_XDPRINTF_("%s: DRHD unit %u - ND capability = %x\n", __func__, drhd_handle, cap.nd);



		//set DRHD root entry table
		if(!xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(&vtd_drhd[drhd_handle], vtd_ret_address)){
			_XDPRINTF_("%s: Halting: error in setting DRHD RET\n", __func__);
			CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		}



		//invalidate caches
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(&vtd_drhd[drhd_handle])){
			_XDPRINTF_("%s: Halting: error in invalidating caches\n", __func__);
			CASM_FUNCCALL(xmhfhw_cpu_hlt, CASM_NOPARAM);
		}



		//enable VT-d translation
#if 1
		xmhfhw_platform_x86pc_vtd_drhd_enable_translation(&vtd_drhd[drhd_handle]);
#endif


		//disable PMRs now (since DMA protection is active via translation)
		xmhfhw_platform_x86pc_vtd_drhd_disable_pmr(&vtd_drhd[drhd_handle]);


		_XDPRINTF_("%s: Successfully setup DRHD unit %u\n", __func__, drhd_handle);
	}

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu32, vtd_dmar_table_physical_address, 0UL);


	_XDPRINTF_("%s: final page-walk level=%u\n", __func__, vtd_pagewalk_level);
}
