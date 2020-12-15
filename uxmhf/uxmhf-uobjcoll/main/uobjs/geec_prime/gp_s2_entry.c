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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec_prime.h>



//@ghost bool cor_gp_s2_initsysmemmap = false;
//@ghost bool cor_gp_s2_sdmenumsysdevices = false;
//@ghost bool cor_gp_s2_sdminitdevmap = false;
//@ghost bool cor_gp_s2_sda = false;
//@ghost bool cor_gp_s2_gathersysmemtypes = false;
//@ghost bool cor_gp_s2_setupiotbl = false;
//@ghost bool cor_gp_s2_setupmpgtblv = false;
//@ghost bool cor_gp_s2_setupmpgtblu = false;
//@ghost bool cor_gp_s2_setupgdt = false;
//@ghost bool cor_gp_s2_setupidt = false;
//@ghost bool cor_gp_s2_setuptss = false;
//@ghost bool cor_gp_s3_entry = false;
/*@
	requires (gp_rwdatahdr.xcbootinfo_store.memmapinfo_numentries < MAX_E820_ENTRIES);
	requires 0 <= vtd_drhd_maxhandle <= VTD_MAX_DRHD;
	requires \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==>
		(0 <= xmhfgeec_slab_info_table[x].incl_devices_count <= XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES);
	requires \forall integer x; 0 <= x < XMHFGEEC_TOTAL_SLABS ==>
		(0 <= xmhfgeec_slab_info_table[x].excl_devices_count <= XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES);

	assigns cor_gp_s2_initsysmemmap;
	assigns cor_gp_s2_sdmenumsysdevices;
	assigns cor_gp_s2_sdminitdevmap;
	assigns cor_gp_s2_sda;
	assigns cor_gp_s2_gathersysmemtypes;
	assigns cor_gp_s2_setupiotbl;
	assigns cor_gp_s2_setupmpgtblv;
	assigns cor_gp_s2_setupmpgtblu;
	assigns cor_gp_s2_setupgdt;
	assigns cor_gp_s2_setupidt;
	assigns cor_gp_s2_setuptss;
	assigns cor_gp_s3_entry;

	ensures (cor_gp_s2_initsysmemmap == true);
	ensures (cor_gp_s2_sdmenumsysdevices == true);
	ensures (cor_gp_s2_sdminitdevmap == true);
	ensures (cor_gp_s2_sda == true);
	ensures (cor_gp_s2_gathersysmemtypes == true);
	ensures (cor_gp_s2_setupiotbl == true);
	ensures (cor_gp_s2_setupmpgtblv == true);
	ensures (cor_gp_s2_setupmpgtblu == true);
	ensures (cor_gp_s2_setupgdt == true);
	ensures (cor_gp_s2_setupidt == true);
	ensures (cor_gp_s2_setuptss == true);
	ensures (cor_gp_s3_entry == true);
@*/
void gp_s2_entry(void){

	// //intialize system memory map
	gp_s2_initsysmemmap();
	// //@ghost cor_gp_s2_initsysmemmap = true;


	// //enumerate system devices
	// //@assert cor_gp_s2_initsysmemmap == true;
	gp_s2_sdmenumsysdevices();
	// //@ghost cor_gp_s2_sdmenumsysdevices = true;


	// //initialize uobj device mapping
	// //@assert cor_gp_s2_initsysmemmap == true;
	// //@assert cor_gp_s2_sdmenumsysdevices == true;
	#if 0
	gp_s2_sdminitdevmap();
	#endif
	// //@ghost cor_gp_s2_sdminitdevmap = true;


	// //setup slab system device allocation and device page tables
	// //@assert (cor_gp_s2_initsysmemmap == true);
	// //@assert cor_gp_s2_sdmenumsysdevices == true;
	// //@assert (cor_gp_s2_sdminitdevmap == true);
	#if 0
	gp_s2_sda();
	#endif
	// //@ghost cor_gp_s2_sda = true;

	// //gather memory types for EPT (for guest slabs)
	// //@assert (cor_gp_s2_initsysmemmap == true);
	// //@assert cor_gp_s2_sdmenumsysdevices == true;
	// //@assert (cor_gp_s2_sdminitdevmap == true);
	// //@assert (cor_gp_s2_sda == true);
	gp_s2_gathersysmemtypes();
	// //@ghost cor_gp_s2_gathersysmemtypes = true;

	// //setup (unverified) slab iotbl
	// //@assert (cor_gp_s2_initsysmemmap == true);
	// //@assert cor_gp_s2_sdmenumsysdevices == true;
	// //@assert (cor_gp_s2_sdminitdevmap == true);
	// //@assert (cor_gp_s2_sda == true);
	// //@assert (cor_gp_s2_gathersysmemtypes == true);
	gp_s2_setupiotbl();
	// //@ghost cor_gp_s2_setupiotbl = true;


	// //setup verified uobj memory page tables
	// //@assert (cor_gp_s2_initsysmemmap == true);
	// //@assert cor_gp_s2_sdmenumsysdevices == true;
	// //@assert (cor_gp_s2_sdminitdevmap == true);
	// //@assert (cor_gp_s2_sda == true);
	// //@assert (cor_gp_s2_gathersysmemtypes == true);
	// //@assert (cor_gp_s2_setupiotbl == true);
	gp_s2_setupmpgtblv();
	// //@ghost cor_gp_s2_setupmpgtblv = true;


	// //setup unverified uobj memory page tables
	// //@assert (cor_gp_s2_initsysmemmap == true);
	// //@assert cor_gp_s2_sdmenumsysdevices == true;
	// //@assert (cor_gp_s2_sdminitdevmap == true);
	// //@assert (cor_gp_s2_sda == true);
	// //@assert (cor_gp_s2_gathersysmemtypes == true);
	// //@assert (cor_gp_s2_setupiotbl == true);
	// //@assert (cor_gp_s2_setupmpgtblv == true);
	#if 0
	gp_s2_setupmpgtblu();
	#endif
	// //@ghost cor_gp_s2_setupmpgtblu = true;

	// //initialize GDT
	// //@assert (cor_gp_s2_initsysmemmap == true);
	// //@assert cor_gp_s2_sdmenumsysdevices == true;
	// //@assert (cor_gp_s2_sdminitdevmap == true);
	// //@assert (cor_gp_s2_sda == true);
	// //@assert (cor_gp_s2_gathersysmemtypes == true);
	// //@assert (cor_gp_s2_setupiotbl == true);
	// //@assert (cor_gp_s2_setupmpgtblv == true);
	// //@assert (cor_gp_s2_setupmpgtblu == true);
	gp_s2_setupgdt();
	// //@ghost cor_gp_s2_setupgdt = true;


	// //initialize IDT
	// //@assert (cor_gp_s2_initsysmemmap == true);
	// //@assert cor_gp_s2_sdmenumsysdevices == true;
	// //@assert (cor_gp_s2_sdminitdevmap == true);
	// //@assert (cor_gp_s2_sda == true);
	// //@assert (cor_gp_s2_gathersysmemtypes == true);
	// //@assert (cor_gp_s2_setupiotbl == true);
	// //@assert (cor_gp_s2_setupmpgtblv == true);
	// //@assert (cor_gp_s2_setupmpgtblu == true);
	// //@assert (cor_gp_s2_setupgdt == true);
	gp_s2_setupidt();
	// //@ghost cor_gp_s2_setupidt = true;


	// //initialize TSS
	// //@assert (cor_gp_s2_initsysmemmap == true);
	// //@assert cor_gp_s2_sdmenumsysdevices == true;
	// //@assert (cor_gp_s2_sdminitdevmap == true);
	// //@assert (cor_gp_s2_sda == true);
	// //@assert (cor_gp_s2_gathersysmemtypes == true);
	// //@assert (cor_gp_s2_setupiotbl == true);
	// //@assert (cor_gp_s2_setupmpgtblv == true);
	// //@assert (cor_gp_s2_setupmpgtblu == true);
	// //@assert (cor_gp_s2_setupgdt == true);
	// //@assert (cor_gp_s2_setupidt == true);
	gp_s2_setuptss();
	// //@ghost cor_gp_s2_setuptss = true;



	//move on to stage-3
	//@assert (cor_gp_s2_initsysmemmap == true);
	//@assert cor_gp_s2_sdmenumsysdevices == true;
	//@assert (cor_gp_s2_sdminitdevmap == true);
	//@assert (cor_gp_s2_sda == true);
	//@assert (cor_gp_s2_gathersysmemtypes == true);
	//@assert (cor_gp_s2_setupiotbl == true);
	//@assert (cor_gp_s2_setupmpgtblv == true);
	//@assert (cor_gp_s2_setupmpgtblu == true);
	//@assert (cor_gp_s2_setupgdt == true);
	//@assert (cor_gp_s2_setupidt == true);
	//@assert (cor_gp_s2_setuptss == true);
	gp_s3_entry();
	//@ghost cor_gp_s3_entry = true;


}

