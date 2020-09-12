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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>

/*@
	requires 0 <= slabid < XMHFGEEC_TOTAL_SLABS;

	behavior setcet4lvl:
		assumes (
				(
				!(	(slabid == 0) ||
					(!_slabdevpgtbl_infotable[slabid].devpgtbl_initialized)  ||
					( !(bus < PCI_BUS_MAX && dev < PCI_DEVICE_MAX && func < PCI_FUNCTION_MAX) )
				) && (pagewalk_lvl == VTD_PAGEWALK_4LEVEL)
				)
			);
		ensures ( _slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[0] ==
			    (vtd_make_cete((uint64_t)&_slabdevpgtbl_pml4t[slabid], VTD_CET_PRESENT))
			);
		ensures ( _slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[1] ==
			    (vtd_make_cetehigh(2, (slabid)))
			);
		ensures (\result == true);


	behavior setcet3lvl:
		assumes (
				(
				!(	(slabid == 0) ||
					(!_slabdevpgtbl_infotable[slabid].devpgtbl_initialized)  ||
					( !(bus < PCI_BUS_MAX && dev < PCI_DEVICE_MAX && func < PCI_FUNCTION_MAX) )
				) && (pagewalk_lvl == VTD_PAGEWALK_3LEVEL)
				)
			);
		ensures ( _slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[0] ==
			    (vtd_make_cete((uint64_t)&_slabdevpgtbl_pdpt[slabid], VTD_CET_PRESENT))
			);
		ensures ( _slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[1] ==
			    (vtd_make_cetehigh(1, (slabid)))
			);
		ensures (\result == true);


	behavior invalid:
		assumes (
				(	(slabid == 0) ||
					(!_slabdevpgtbl_infotable[slabid].devpgtbl_initialized)  ||
					( !(bus < PCI_BUS_MAX && dev < PCI_DEVICE_MAX && func < PCI_FUNCTION_MAX) )
				) ||

				(
				!(	(slabid == 0) ||
					(!_slabdevpgtbl_infotable[slabid].devpgtbl_initialized)  ||
					( !(bus < PCI_BUS_MAX && dev < PCI_DEVICE_MAX && func < PCI_FUNCTION_MAX) )
				) && !(pagewalk_lvl == VTD_PAGEWALK_4LEVEL) &&
					!(pagewalk_lvl == VTD_PAGEWALK_3LEVEL)
				)

			);
		ensures (\result == false);

	complete behaviors;
	disjoint behaviors;
@*/

bool gp_s2_sdabinddevice(uint32_t slabid, uint32_t pagewalk_lvl,  uint32_t bus, uint32_t dev, uint32_t func){
	bool retstatus=false;

	if(	(slabid == 0) ||
		(!_slabdevpgtbl_infotable[slabid].devpgtbl_initialized)  ||
		( !(bus < PCI_BUS_MAX && dev < PCI_DEVICE_MAX && func < PCI_FUNCTION_MAX) )
 	){
		_XDPRINTF_("%s: Error: slabid (%u) is sentinel, devpgtbl not initialized or b:d:f out of limits\n",  __func__, slabid);
		retstatus = false;
	}else{

		//b is our index into ret
		// (d* PCI_FUNCTION_MAX) + f = index into the cet
		if(pagewalk_lvl == VTD_PAGEWALK_4LEVEL){
			_slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[0] =
			    vtd_make_cete((uint64_t)&_slabdevpgtbl_pml4t[slabid], VTD_CET_PRESENT);
			_slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[1] =
			    vtd_make_cetehigh(2, (slabid));
			_XDPRINTF_("%s: CET, 4-lvl[%u][%u]: h=0x%016llx, l=0x%016llx\n",  __func__,
					bus,
					((dev*PCI_FUNCTION_MAX) + func),
					_slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[1],
					_slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[0]);

			retstatus = true;
		}else if (pagewalk_lvl == VTD_PAGEWALK_3LEVEL){
			_slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[0] =
			    vtd_make_cete((uint64_t)&_slabdevpgtbl_pdpt[slabid], VTD_CET_PRESENT);
			_slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[1] =
			    vtd_make_cetehigh(1, (slabid));
			_XDPRINTF_("%s: CET, 3-lvl[%u][%u]: h=0x%016llx, l=0x%016llx\n",  __func__,
					bus,
					((dev*PCI_FUNCTION_MAX) + func),
					_slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[1],
					_slabdevpgtbl_vtd_cet[bus][((dev*PCI_FUNCTION_MAX) + func)].qwords[0]);

			retstatus = true;
		}else{ //unknown page walk length, fail
			_XDPRINTF_("%s: Error: slabid (%u) unknown pagewalk\n",  __func__, slabid);
			retstatus = false;
		}

	}

	return retstatus;
}


