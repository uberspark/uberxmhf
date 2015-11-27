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


#include <xmhf.h>
#include <xmhf-hwm.h>



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
		.reg_cap= 0,
		.reg_ecap= 0,
		.reg_rtaddr= 0,
		.reg_ccmd= 0,
		.reg_phmbase= 0,
		.reg_phmlimit= 0,
		.reg_iotlb= 0,
		.reg_iva= 0,
		.regbaseaddr=0xfed90000ULL,
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
		.reg_cap= 0,
		.reg_ecap= 0,
		.reg_rtaddr= 0,
		.reg_ccmd= 0,
		.reg_phmbase= 0,
		.reg_phmlimit= 0,
		.reg_iotlb= 0,
		.reg_iva= 0,
		.regbaseaddr=0xfed91000ULL,
	},

};

u32 xmhfhwm_vtd_total_drhdunits = (sizeof(xmhfhwm_vtd_drhd_state)/sizeof(xmhfhwm_vtd_drhd_state[0]));


bool _impl_xmhfhwm_vtd_read(u32 sysmemaddr, sysmem_read_t readsize, u64 *read_result){
	bool retval = false;

	//@assert xmhfhwm_vtd_total_drhdunits == 2;
	return retval;
}


