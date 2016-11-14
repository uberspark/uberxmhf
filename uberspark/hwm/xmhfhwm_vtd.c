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
 * x86 cpu txt implementation
 * author: amit vasudevan (amitvasudevan@acm.org)
*/


#include <uberspark.h>


xmhfhwm_vtd_drhd_state_t xmhfhwm_vtd_drhd_state[] = {
	{
		.reg_ver= 0,
		.reg_gcmd= 0,
		.reg_gsts= 0,
		.reg_fsts= 0,
		.reg_fectl= 0,
		.reg_pmen= 0,
		.reg_plmbase= 0,
		.reg_plmlimit= 0,
		.reg_cap_lo= 0x20660462,
		.reg_cap_hi= 0x00c00000,
		.reg_ecap_lo= 0x00f0101a,
		.reg_ecap_hi= 0,
		.reg_rtaddr_lo= 0,
		.reg_rtaddr_hi= 0,
		.reg_ccmd_lo= 0,
		.reg_ccmd_hi= 0,
		.reg_phmbase_lo= 0,
		.reg_phmbase_hi= 0,
		.reg_phmlimit_lo= 0,
		.reg_phmlimit_hi= 0,
		.reg_iotlb_lo= 0,
		.reg_iotlb_hi= 0,
		.reg_iva_lo= 0,
		.reg_iva_hi= 0,
		.regbaseaddr=0xfed90000ULL,
		.iotlbaddr=0xfed90108ULL,
		.ivaaddr=0xfed90100ULL,
	},


	{
		.reg_ver= 0,
		.reg_gcmd= 0,
		.reg_gsts= 0,
		.reg_fsts= 0,
		.reg_fectl= 0,
		.reg_pmen= 0,
		.reg_plmbase= 0,
		.reg_plmlimit= 0,
		.reg_cap_lo= 0x20660462,
		.reg_cap_hi= 0x00d20080,
		.reg_ecap_lo= 0x000f010da,
		.reg_ecap_hi= 0,
		.reg_rtaddr_lo= 0,
		.reg_rtaddr_hi= 0,
		.reg_ccmd_lo= 0,
		.reg_ccmd_hi= 0,
		.reg_phmbase_lo= 0,
		.reg_phmbase_hi= 0,
		.reg_phmlimit_lo= 0,
		.reg_phmlimit_hi= 0,
		.reg_iotlb_lo= 0,
		.reg_iotlb_hi= 0,
		.reg_iva_lo= 0,
		.reg_iva_hi= 0,
		.regbaseaddr=0xfed91000ULL,
		.iotlbaddr=0xfed91108ULL,
		.ivaaddr=0xfed91100ULL,
	},

};

u32 xmhfhwm_vtd_total_drhdunits = (sizeof(xmhfhwm_vtd_drhd_state)/sizeof(xmhfhwm_vtd_drhd_state[0]));


bool _impl_xmhfhwm_vtd_read(u32 sysmemaddr, sysmem_read_t readsize, u64 *read_result){
	bool retval = false;
	u32 i;

	for(i=0; i < xmhfhwm_vtd_total_drhdunits; i++){

		if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_VER_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_ver;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_GCMD_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_gcmd;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_GSTS_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_gsts;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_FSTS_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_fsts;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_FECTL_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_fectl;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PMEN_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_pmen;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PLMBASE_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_plmbase;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PLMLIMIT_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_plmlimit;
			retval = true;
			break;


		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_CAP_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_cap_lo;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_CAP_REG_OFF + 0x4){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_cap_hi;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_ECAP_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_ecap_lo;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_ECAP_REG_OFF + 0x4){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_ecap_hi;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_RTADDR_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_rtaddr_lo;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_RTADDR_REG_OFF + 0x4){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_rtaddr_hi;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_CCMD_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_ccmd_lo;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_CCMD_REG_OFF + 0x4){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_ccmd_hi;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PHMBASE_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_phmbase_lo;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PHMBASE_REG_OFF + 0x4){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_phmbase_hi;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PHMLIMIT_REG_OFF){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_phmlimit_lo;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PHMLIMIT_REG_OFF + 0x4){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_phmlimit_hi;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].iotlbaddr){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_iotlb_lo;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].iotlbaddr + 0x4){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_iotlb_hi;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].ivaaddr){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_iva_lo;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].ivaaddr + 0x4){
			//@assert readsize == SYSMEMREADU32;
			*read_result = (u64)xmhfhwm_vtd_drhd_state[i].reg_iva_hi;
			retval = true;
			break;

		} else {

		}
	}

	return retval;
}


bool _impl_xmhfhwm_vtd_write(u32 sysmemaddr, sysmem_write_t writesize, u64 write_value){
	bool retval = false;
	u32 i;

	for(i=0; i < xmhfhwm_vtd_total_drhdunits; i++){

		if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_VER_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_ver = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_GCMD_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_gcmd = (u32)write_value;
			if(xmhfhwm_vtd_drhd_state[i].reg_gcmd & 0x80000000UL){
				//te enabled
				//so..set gsts bit 31 to 1
				xmhfhwm_vtd_drhd_state[i].reg_gsts |= 0x80000000UL;
			}
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_GSTS_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_gsts = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_FSTS_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_fsts = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_FECTL_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_fectl = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PMEN_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_pmen = (u32)write_value;
			if(!(xmhfhwm_vtd_drhd_state[i].reg_pmen & 0x80000000UL))
				xmhfhwm_vtd_drhd_state[i].reg_pmen &= ~(0x00000001UL);

			if(xmhfhwm_vtd_drhd_state[i].reg_pmen & 0x80000000UL)
				xmhfhwm_vtd_drhd_state[i].reg_pmen |= 0x00000001UL;

			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PLMBASE_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_plmbase = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PLMLIMIT_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_plmlimit = (u32)write_value;
			retval = true;
			break;


		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_CAP_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_cap_lo = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_CAP_REG_OFF + 0x4){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_cap_hi = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_ECAP_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_ecap_lo = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_ECAP_REG_OFF + 0x4){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_ecap_hi = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_RTADDR_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_rtaddr_lo = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_RTADDR_REG_OFF + 0x4){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_rtaddr_hi = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_CCMD_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_ccmd_lo = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_CCMD_REG_OFF + 0x4){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_ccmd_hi = (u32)write_value;
			if(xmhfhwm_vtd_drhd_state[i].reg_ccmd_hi & (0x80000000UL)){
				//icc is set (bit 31)
				//so..set caig (28, 27) to cirg (30, 29)
				//and clear icc
                                //cirg bit 30 mask = 0x40000000UL
                                //cirg bit 29 mask = 0x20000000UL
                                //caig bit 28 mas = 0x10000000UL
                                //caig bit 27 mask = 0x08000000UL
				if(xmhfhwm_vtd_drhd_state[i].reg_ccmd_hi & 0x40000000UL)
					xmhfhwm_vtd_drhd_state[i].reg_ccmd_hi |= 0x10000000UL;
				else
					xmhfhwm_vtd_drhd_state[i].reg_ccmd_hi &= ~(0x10000000UL);

				if(xmhfhwm_vtd_drhd_state[i].reg_ccmd_hi & 0x20000000UL)
					xmhfhwm_vtd_drhd_state[i].reg_ccmd_hi |= 0x08000000UL;
				else
					xmhfhwm_vtd_drhd_state[i].reg_ccmd_hi &= ~(0x08000000UL);

                                xmhfhwm_vtd_drhd_state[i].reg_ccmd_hi &= ~(0x80000000UL);
			}
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PHMBASE_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_phmbase_lo = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PHMBASE_REG_OFF + 0x4){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_phmbase_hi = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PHMLIMIT_REG_OFF){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_phmlimit_lo = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].regbaseaddr +   VTD_PHMLIMIT_REG_OFF + 0x4){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_phmlimit_hi = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].iotlbaddr){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_iotlb_lo = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].iotlbaddr + 0x4){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_iotlb_hi = (u32)write_value;
			if(xmhfhwm_vtd_drhd_state[i].reg_iotlb_hi & (0x80000000UL)){
				//ivt is set (bit 31)
				//so..set iaig (26, 25) to iirg (29, 28)
				//and clear ivt
                                //iirg bit 29 mask = 0x20000000UL
                                //iirg bit 28 mask = 0x10000000UL
                                //iaig bit 26 mask = 0x04000000UL
                                //iaig bit 25 mask = 0x02000000UL
				if(xmhfhwm_vtd_drhd_state[i].reg_iotlb_hi & 0x20000000UL)
					xmhfhwm_vtd_drhd_state[i].reg_iotlb_hi |= 0x04000000UL;
				else
					xmhfhwm_vtd_drhd_state[i].reg_iotlb_hi &= ~(0x04000000UL);

				if(xmhfhwm_vtd_drhd_state[i].reg_iotlb_hi & 0x10000000UL)
					xmhfhwm_vtd_drhd_state[i].reg_iotlb_hi |= 0x02000000UL;
				else
					xmhfhwm_vtd_drhd_state[i].reg_iotlb_hi &= ~(0x02000000UL);

                                xmhfhwm_vtd_drhd_state[i].reg_iotlb_hi &= ~(0x80000000UL);
			}


			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].ivaaddr){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_iva_lo = (u32)write_value;
			retval = true;
			break;

		} else if(sysmemaddr == (u32)xmhfhwm_vtd_drhd_state[i].ivaaddr + 0x4){
			//@assert writesize == SYSMEMWRITEU32;
			xmhfhwm_vtd_drhd_state[i].reg_iva_hi = (u32)write_value;
			retval = true;
			break;

		} else {

		}
	}



	return retval;
}

