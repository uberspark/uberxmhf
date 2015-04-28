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
#include <uapi_slabdevpgtbl.h>
#include <geec_primesmp.h>

__attribute__((aligned(4096))) static u64 _xcprimeon_init_pdt[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
__attribute__((aligned(4096))) static u64 _xcprimeon_init_pdpt[PAE_MAXPTRS_PER_PDPT];

static void xmhfhic_setupinitpgtables(void){
    u32 paddr=0;
    u32 i, j;
    u64 pdpe_flags = (_PAGE_PRESENT);
    u64 pdte_flags = (_PAGE_RW | _PAGE_PSE | _PAGE_PRESENT);

    memset(&_xcprimeon_init_pdpt, 0, sizeof(_xcprimeon_init_pdpt));

    /*_XDPRINTF_("_xcprimeon_init_pdt size=%u\n", sizeof(_xcprimeon_init_pdt));
    _XDPRINTF_("_xcprimeon_init_pdpt size=%u\n", sizeof(_xcprimeon_init_pdpt));
*/

    for(i=0; i < PAE_PTRS_PER_PDPT; i++){
        u64 entry_addr = (u64)&_xcprimeon_init_pdt[i][0];
        _xcprimeon_init_pdpt[i] = pae_make_pdpe(entry_addr, pdpe_flags);

        for(j=0; j < PAE_PTRS_PER_PDT; j++){
            if(paddr == 0xfee00000 || paddr == 0xfec00000)
                _xcprimeon_init_pdt[i][j] = pae_make_pde_big(paddr, (pdte_flags | _PAGE_PCD));
            else
                _xcprimeon_init_pdt[i][j] = pae_make_pde_big(paddr, pdte_flags);

            paddr += PAGE_SIZE_2M;
        }
    }

    //debug
    /*_XDPRINTF_("page-table dump:\n");

    for(i=0; i < PAE_PTRS_PER_PDPT; i++){
        _XDPRINTF_("pdpd[%u]=%016llx\n\n", i, _xcprimeon_init_pdpt[i]);

        for(j=0; j < PAE_PTRS_PER_PDT; j++)
            _XDPRINTF_("pdt[%u][%u]=%016llx\n", i, j, _xcprimeon_init_pdt[i][j]);
    }*/

    {
        _XDPRINTF_("fn:%s, line:%u\n", __func__, __LINE__);
 CASM_FUNCCALL(wrmsr64,MSR_EFER, (rdmsr64(MSR_EFER) | (0x800)) );
        _XDPRINTF_("EFER=%016llx\n", CASM_FUNCCALL(rdmsr64,MSR_EFER));
 CASM_FUNCCALL(write_cr4,read_cr4(CASM_NOPARAM) | (0x30) );
        _XDPRINTF_("CR4=%08x\n", CASM_FUNCCALL(read_cr4,CASM_NOPARAM));
 CASM_FUNCCALL(write_cr3,(u32)&_xcprimeon_init_pdpt);
        _XDPRINTF_("CR3=%08x\n", CASM_FUNCCALL(read_cr3,CASM_NOPARAM));
 CASM_FUNCCALL(write_cr0,0x80000015);
        _XDPRINTF_("fn:%s, line:%u\n", __func__, __LINE__);
    }

}











void _geec_prime_main(slab_params_t *sp){
    u64 pgtblbase;

#if !defined(__XMHF_VERIFICATION__)
	//initialize debugging early on
	xmhfhw_platform_serial_init((char *)&xcbootinfo->debugcontrol_buffer);


	//[debug] print relevant startup info.
	_XDPRINTF_("%s: alive and starting...\n", __func__);

	_XDPRINTF_("    xcbootinfo at = 0x%08x\n", (u32)xcbootinfo);
	_XDPRINTF_("	numE820Entries=%u\n", xcbootinfo->memmapinfo_numentries);
	_XDPRINTF_("	system memory map buffer at 0x%08x\n", (u32)&xcbootinfo->memmapinfo_buffer);
	_XDPRINTF_("	numCPUEntries=%u\n", xcbootinfo->cpuinfo_numentries);
	_XDPRINTF_("	cpuinfo buffer at 0x%08x\n", (u32)&xcbootinfo->cpuinfo_buffer);
	_XDPRINTF_("	XMHF size= %u bytes\n", __TARGET_SIZE_XMHF);
	_XDPRINTF_("	OS bootmodule at 0x%08x, size=%u bytes\n",
		xcbootinfo->richguest_bootmodule_base, xcbootinfo->richguest_bootmodule_size);
    _XDPRINTF_("\tcmdline = \"%s\"\n", xcbootinfo->cmdline_buffer);
	_XDPRINTF_("SL: runtime at 0x%08x; size=0x%08x bytes\n", __TARGET_BASE_XMHF, __TARGET_SIZE_XMHF);
	_XDPRINTF_("SL: XMHF_BOOTINFO at 0x%08x, magic=0x%08x\n", (u32)xcbootinfo, xcbootinfo->magic);
	HALT_ON_ERRORCOND(xcbootinfo->magic == RUNTIME_PARAMETER_BLOCK_MAGIC);
 	_XDPRINTF_("\nNumber of E820 entries = %u", xcbootinfo->memmapinfo_numentries);
	{
		u32 i;
		for(i=0; i < (u32)xcbootinfo->memmapinfo_numentries; i++){
			_XDPRINTF_("\n0x%08x%08x, size=0x%08x%08x (%u)",
			  xcbootinfo->memmapinfo_buffer[i].baseaddr_high, xcbootinfo->memmapinfo_buffer[i].baseaddr_low,
			  xcbootinfo->memmapinfo_buffer[i].length_high, xcbootinfo->memmapinfo_buffer[i].length_low,
			  xcbootinfo->memmapinfo_buffer[i].type);
		}
  	}
#endif

    //HALT();

    _XDPRINTF_("Proceeding to setup init pagetables...\n");
    xmhfhic_setupinitpgtables();
    _XDPRINTF_("Init page table setup.\n");


    //initialize slab info table based on setup data
    xmhfhic_arch_setup_slab_info();

    //sanity check HIC (hardware) requirements
    xmhfhic_arch_sanity_check_requirements();


#if !defined (__XMHF_VERIFICATION__)
    //setup slab system device allocation and device page tables
        xmhfhic_arch_setup_slab_device_allocation();

    //setup slab memory page tables
    xmhfhic_arch_setup_slab_mem_page_tables();
#endif //__XMHF_VERIFICATION__

    //switch to prime page tables
    _XDPRINTF_("Proceeding to switch to GEEC_PRIME pagetables...\n");
    CASM_FUNCCALL(write_cr3,(u32)_xmhfhic_common_slab_info_table[XMHFGEEC_SLAB_GEEC_PRIME].mempgtbl_cr3);
    _XDPRINTF_("Switched to GEEC_PRIME pagetables...\n");

    //transfer control to geec_primesmp
    {
        slab_params_t spl;
        spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
        spl.dst_slabid = XMHFGEEC_SLAB_GEEC_PRIMESMP;
        spl.dst_uapifn = 0;
        spl.cpuid = 0;
        XMHF_SLAB_CALLNEW(&spl);
    }

    //we should never get here
    _XDPRINTF_("Should never be here. Halting!\n");
    HALT();
}




////////////////////////////////////////////////////////////
// setup slab info

void xmhfhic_arch_setup_slab_info(void){

    //initialize slab info table
    {
        u32 i;

        for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){

/*            _xmhfhic_common_slab_info_table[i].slab_inuse = true;
            _xmhfhic_common_slab_info_table[i].slab_privilegemask =
                _xmhfhic_init_setupdata_slab_caps[i].slab_privilegemask;
            _xmhfhic_common_slab_info_table[i].slab_callcaps =
                _xmhfhic_init_setupdata_slab_caps[i].slab_callcaps;
            _xmhfhic_common_slab_info_table[i].slab_uapicaps =
                _xmhfhic_init_setupdata_slab_caps[i].slab_uapicaps;


            #if !defined(__XMHF_VERIFICATION__)
            memcpy(&_xmhfhic_common_slab_info_table[i].slab_devices,
                   &_xmhfhic_init_setupdata_slab_caps[i].slab_devices,
                   sizeof(_xmhfhic_common_slab_info_table[0].slab_devices));

            memcpy(_xmhfhic_common_slab_info_table[i].slab_physmem_extents,
                   _xmhfhic_init_setupdata_slab_physmem_extents[i],
                   sizeof(_xmhfhic_common_slab_info_table[0].slab_physmem_extents));
            #endif

            _xmhfhic_common_slab_info_table[i].entrystub = _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_start;

            //arch. specific
            _xmhfhic_common_slab_info_table[i].slabtype =
                _xmhfhic_init_setupdata_slab_caps[i].slab_archparams;

            _xmhfhic_common_slab_info_table[i].mempgtbl_initialized=false;
            _xmhfhic_common_slab_info_table[i].devpgtbl_initialized=false;
*/
/*            #if !defined(__XMHF_VERIFICATION__)
            {
                u32 j;
                //u64 *slab_stackhdr = (u64 *)_xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_start;
                u32 *slab_stackhdr = (u32 *)_xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_start;

                if(slab_stackhdr){
                    for(j=0; j < MAX_PLATFORM_CPUS; j++)
                        _xmhfhic_common_slab_info_table[i].slabtos[j]=slab_stackhdr[j];
                }
            }
            #endif
*/
        }
    }


    //#if !defined (__XMHF_VERIFICATION__)
    ////initialize HIC physical memory extents
    //memcpy(_xmhfhic_common_hic_physmem_extents,
    //       _xmhfhic_init_setupdata_hic_physmem_extents,
    //       sizeof(_xmhfhic_common_hic_physmem_extents));
    //#endif

    #if !defined (__XMHF_VERIFICATION__)
	////print out HIC section information
    //{
	//	_XDPRINTF_("xmhfhic section info:\n");
	//	_XDPRINTF_("  xmhfhic sharedro(%08x-%08x)\n", _xmhfhic_common_hic_physmem_extents[0].addr_start, _xmhfhic_common_hic_physmem_extents[0].addr_end);
	//	_XDPRINTF_("  xmhfhic code(%08x-%08x)\n", _xmhfhic_common_hic_physmem_extents[1].addr_start, _xmhfhic_common_hic_physmem_extents[1].addr_end);
	//	_XDPRINTF_("  xmhfhic rwdata(%08x-%08x)\n", _xmhfhic_common_hic_physmem_extents[2].addr_start, _xmhfhic_common_hic_physmem_extents[2].addr_end);
	//	_XDPRINTF_("  xmhfhic rodata(%08x-%08x)\n", _xmhfhic_common_hic_physmem_extents[3].addr_start, _xmhfhic_common_hic_physmem_extents[3].addr_end);
	//	_XDPRINTF_("  xmhfhic stack(%08x-%08x)\n", _xmhfhic_common_hic_physmem_extents[4].addr_start, _xmhfhic_common_hic_physmem_extents[4].addr_end);
    //
    //}

	//print out slab table
	{
			u32 i;

			for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
				_XDPRINTF_("slab %u: dumping slab header\n", i);
				_XDPRINTF_("	slabtype=%08x\n", _xmhfhic_common_slab_info_table[i].slabtype);
				_XDPRINTF_("	slab_inuse=%s\n", ( _xmhfhic_common_slab_info_table[i].slab_inuse ? "true" : "false") );
				_XDPRINTF_("	slab_callcaps=%08x\n", _xmhfhic_common_slab_info_table[i].slab_callcaps);
				_XDPRINTF_("	slab_devices=%s\n", ( _xmhfhic_common_slab_info_table[i].slab_devices.desc_valid ? "true" : "false") );
				_XDPRINTF_("	slab_pgtblbase=%x\n", ( _xmhfhic_common_slab_info_table[i].mempgtbl_cr3) );
				_XDPRINTF_("  slab_code(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_end);
				_XDPRINTF_("  slab_data(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[1].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[1].addr_end);
				_XDPRINTF_("  slab_stack(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_end);
				_XDPRINTF_("  slab_dmadata(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_end);
				_XDPRINTF_("  slab_mmio(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[4].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[4].addr_end);
				_XDPRINTF_("  slab_entrystub=%08x\n", _xmhfhic_common_slab_info_table[i].entrystub);

                {
                    u32 j;

                    for(j=0; j < MAX_PLATFORM_CPUS; j++)
                        //_XDPRINTF_("     CPU %u: stack TOS=%016llx\n", j,
                        //       _xmhfhic_common_slab_info_table[i].slabtos[j]);
                        _XDPRINTF_("     CPU %u: stack TOS=%08x\n", j,
                               _xmhfhic_common_slab_info_table[i].slabtos[j]);
                }

		}
	}
    #endif



}








///////////////////////////////////////////////////////////////
// sanity check HIC (hardware) requirements
void xmhfhic_arch_sanity_check_requirements(void){
	u32 cpu_vendor;

	//grab CPU vendor
	cpu_vendor = xmhf_baseplatform_arch_getcpuvendor();
	if (cpu_vendor != CPU_VENDOR_INTEL){
		_XDPRINTF_("%s: not an Intel CPU but running VMX backend. Halting!\n", __func__);
		HALT();
	}

	//check VMX support
	{
		u32	cpu_features;
		u32 res0,res1,res2;

 CASM_FUNCCALL(xmhfhw_cpu_cpuid,0x1, &res0, &res1, &cpu_features, &res2);

		if ( ( cpu_features & (1<<5) ) == 0 ){
			_XDPRINTF_("No VMX support. Halting!\n");
			HALT();
		}
	}

	//we require unrestricted guest and EPT support, bail out if we don't have it
    {
        u64 msr_procctls2 = CASM_FUNCCALL(rdmsr64,IA32_VMX_PROCBASED_CTLS2_MSR);
        if( !( (msr_procctls2 >> 32) & 0x80 ) ){
            _XDPRINTF_("%s: need unrestricted guest support but did not find any!\n", __func__);
            HALT();
        }

        if( !( (msr_procctls2 >> 32) & 0x2) ){
            _XDPRINTF_("%s: need EPTt support but did not find any!\n", __func__);
            HALT();
        }

    }


}























//////////////////////////////////////////////////////////////////////////////
//setup slab device allocation (sda)

//DMA Remapping Hardware Unit Definitions
static VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
static u32 vtd_num_drhd=0;	//total number of DMAR h/w units
static bool vtd_drhd_scanned=false;	//set to true once DRHD units have been scanned in the system

//scan for available DRHD units on the platform and populate the
//global variables set:
//vtd_drhd[] (struct representing a DRHD unit)
//vtd_num_drhd (number of DRHD units detected)
//vtd_dmar_table_physical_address (physical address of the DMAR table)
//returns: true if all is fine else false; dmar_phys_addr_var contains
//max. value of DRHD unit handle (0 through maxhandle-1 are valid handles
//that can subsequently be passed to any of the other vtd drhd functions)
//physical address of the DMAR table in the system
static bool xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(vtd_drhd_handle_t *maxhandle, u32 *dmar_phys_addr_var){
	ACPI_RSDP rsdp;
	ACPI_RSDT rsdt;
	u32 num_rsdtentries;
	u32 rsdtentries[ACPI_MAX_RSDT_ENTRIES];
	u32 status;
	VTD_DMAR dmar;
	u32 i, dmarfound;
	u32 remappingstructuresaddrphys;
	u32 vtd_dmar_table_physical_address;

	//zero out rsdp and rsdt structures
	//memset(&rsdp, 0, sizeof(ACPI_RSDP));
	//memset(&rsdt, 0, sizeof(ACPI_RSDT));
	//sanity check NULL parameter
	if (dmar_phys_addr_var == NULL || maxhandle == NULL)
		return false;

	//set maxhandle to 0 to start with. if we have any errors before
	//we finalize maxhandle we can just bail out
	*maxhandle=0;

	//get ACPI RSDP
	status=xmhfhw_platform_x86pc_acpi_getRSDP(&rsdp);
	if(status == 0)
		return false;

	//_XDPRINTF_("\n%s: RSDP at %08x", __func__, status);

	//grab ACPI RSDT
	xmhfhw_sysmemaccess_copy((u8 *)&rsdt, (u8 *)rsdp.rsdtaddress, sizeof(ACPI_RSDT));
	//_XDPRINTF_("\n%s: RSDT at %08x, len=%u bytes, hdrlen=%u bytes",
	//	__func__, rsdp.rsdtaddress, rsdt.length, sizeof(ACPI_RSDT));

	//get the RSDT entry list
	num_rsdtentries = (rsdt.length - sizeof(ACPI_RSDT))/ sizeof(u32);
	if(num_rsdtentries >= ACPI_MAX_RSDT_ENTRIES){
			//_XDPRINTF_("\n%s: Error num_rsdtentries(%u) > ACPI_MAX_RSDT_ENTRIES (%u)", __func__, num_rsdtentries, ACPI_MAX_RSDT_ENTRIES);
			return false;
	}

	xmhfhw_sysmemaccess_copy((u8 *)&rsdtentries, (u8 *)(rsdp.rsdtaddress + sizeof(ACPI_RSDT)),
			sizeof(u32)*num_rsdtentries);
	//_XDPRINTF_("\n%s: RSDT entry list at %08x, len=%u", __func__,
	//	(rsdp.rsdtaddress + sizeof(ACPI_RSDT)), num_rsdtentries);

	//find the VT-d DMAR table in the list (if any)
	for(i=0; i< num_rsdtentries; i++){
		xmhfhw_sysmemaccess_copy((u8 *)&dmar, (u8 *)rsdtentries[i], sizeof(VTD_DMAR));
		if(dmar.signature == VTD_DMAR_SIGNATURE){
		  dmarfound=1;
		  break;
		}
	}

	//if no DMAR table, bail out
	if(!dmarfound){
		//_XDPRINTF_("\n%s: Error No DMAR table", __func__);
		return false;
	}

	vtd_dmar_table_physical_address = rsdtentries[i]; //DMAR table physical memory address;
	*dmar_phys_addr_var = vtd_dmar_table_physical_address; //store it in supplied argument
	//_XDPRINTF_("\n%s: DMAR at %08x", __func__, vtd_dmar_table_physical_address);

	//detect DRHDs in the DMAR table
	i=0;
	remappingstructuresaddrphys=vtd_dmar_table_physical_address+sizeof(VTD_DMAR);
	//_XDPRINTF_("\n%s: remapping structures at %08x", __func__, remappingstructuresaddrphys);

	while(i < (dmar.length-sizeof(VTD_DMAR))){
		u16 type, length;
		xmhfhw_sysmemaccess_copy((u8 *)&type, (u8 *)(remappingstructuresaddrphys+i), sizeof(u16));
		xmhfhw_sysmemaccess_copy((u8 *)&length, (u8 *)(remappingstructuresaddrphys+i+sizeof(u16)), sizeof(u16));

		switch(type){
			case  0:  //DRHD
				//_XDPRINTF_("\nDRHD at %08x, len=%u bytes", (u32)(remappingstructuresaddrphys+i), length);
				if(vtd_num_drhd >= VTD_MAX_DRHD){
						//_XDPRINTF_("\n%s: Error vtd_num_drhd (%u) > VTD_MAX_DRHD (%u)", __func__, vtd_num_drhd, VTD_MAX_DRHD);
						return false;
				}
				xmhfhw_sysmemaccess_copy((u8 *)&vtd_drhd[vtd_num_drhd], (u8 *)(remappingstructuresaddrphys+i), length);
				vtd_num_drhd++;
				i+=(u32)length;
				break;

			default:	//unknown type, we skip this
				i += (u32)length;
				break;
		}
	}
    _XDPRINTF_("%s: total DRHDs detected= %u units\n", __func__, vtd_num_drhd);

    //populate IVA and IOTLB register addresses within all the DRHD unit
    //structures
    for(i=0; i < vtd_num_drhd; i++){
        VTD_ECAP_REG ecap;

        //ecap.value = _vtd_reg_read(&vtd_drhd[i], VTD_ECAP_REG_OFF);
        unpack_VTD_ECAP_REG(&ecap, _vtd_reg_read(&vtd_drhd[i], VTD_ECAP_REG_OFF));
        vtd_drhd[i].iotlb_regaddr= vtd_drhd[i].regbaseaddr+(ecap.iro*16)+0x8;
        vtd_drhd[i].iva_regaddr= vtd_drhd[i].regbaseaddr+(ecap.iro*16);
	}



	//[DEBUG]: be a little verbose about what we found
	//_XDPRINTF_("\n%s: DMAR Devices:", __func__);
	for(i=0; i < vtd_num_drhd; i++){
		VTD_CAP_REG cap;
		VTD_ECAP_REG ecap;
		_XDPRINTF_("	Device %u on PCI seg %04x; base=0x%016llx\n", i,
					vtd_drhd[i].pcisegment, vtd_drhd[i].regbaseaddr);
		unpack_VTD_CAP_REG(&cap, _vtd_reg_read(&vtd_drhd[i], VTD_CAP_REG_OFF));
		_XDPRINTF_("		cap=0x%016llx\n", pack_VTD_CAP_REG(&cap));
		//ecap.value = _vtd_reg_read(&vtd_drhd[i], VTD_ECAP_REG_OFF);
		unpack_VTD_ECAP_REG(&ecap, _vtd_reg_read(&vtd_drhd[i], VTD_ECAP_REG_OFF));
		_XDPRINTF_("		ecap=0x%016llx\n", (u64)pack_VTD_ECAP_REG(&ecap));
		_XDPRINTF_("	iotlb_regaddr=%08x, iva_regaddr=%08x\n",
					vtd_drhd[i].iotlb_regaddr, vtd_drhd[i].iva_regaddr);

	}

	*maxhandle = vtd_num_drhd;
	vtd_drhd_scanned = true;

	return true;
}

//initialize vtd hardware and return vt-d pagewalk level
static u32 _geec_prime_vtd_initialize(u32 vtd_ret_addr){
    u32 vtd_pagewalk_level = VTD_PAGEWALK_NONE;
    vtd_drhd_handle_t vtd_drhd_maxhandle=0;
	vtd_drhd_handle_t drhd_handle;
	u32 vtd_dmar_table_physical_address=0;
    vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
    u32 i, b, d, f;

	//scan for available DRHD units in the platform
	if(!xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(&vtd_drhd_maxhandle, &vtd_dmar_table_physical_address)){
        _XDPRINTF_("%s: unable to scan for DRHD units. halting!\n", __func__);
		HALT();
	}

    _XDPRINTF_("%s: maxhandle = %u, dmar table addr=0x%08x\n", __func__,
                (u32)vtd_drhd_maxhandle, (u32)vtd_dmar_table_physical_address);


	//initialize all DRHD units
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
   		VTD_CAP_REG cap;

		_XDPRINTF_("%s: Setting up DRHD unit %u...\n", __func__, drhd_handle);

		if(!xmhfhw_platform_x86pc_vtd_drhd_initialize(&vtd_drhd[drhd_handle]) ){
            _XDPRINTF_("%s: error setting up DRHD unit %u. halting!\n", __func__, drhd_handle);
			HALT();
		}

        //read and store DRHD supported page-walk length
        unpack_VTD_CAP_REG(&cap, xmhfhw_platform_x86pc_vtd_drhd_reg_read(&vtd_drhd[drhd_handle], VTD_CAP_REG_OFF));
        if(cap.sagaw & 0x2){
            if(vtd_pagewalk_level == VTD_PAGEWALK_NONE || vtd_pagewalk_level == VTD_PAGEWALK_3LEVEL){
                vtd_pagewalk_level = VTD_PAGEWALK_3LEVEL;
                _XDPRINTF_("%s: DRHD unit %u - 3-level page-walk\n", __func__, drhd_handle);
            }else{
                _XDPRINTF_("%s: Halting: mixed hardware supported page-walk lengths\n",
                            __func__);
                HALT();
            }
        }

        if(cap.sagaw & 0x4){
            if(vtd_pagewalk_level == VTD_PAGEWALK_NONE || vtd_pagewalk_level == VTD_PAGEWALK_4LEVEL){
                vtd_pagewalk_level = VTD_PAGEWALK_4LEVEL;
                _XDPRINTF_("%s: DRHD unit %u - 4-level page-walk\n", __func__, drhd_handle);
            }else{
                _XDPRINTF_("%s: Halting: mixed hardware supported page-walk lengths\n",
                            __func__);
                HALT();
            }
        }


		//set DRHD root entry table
		if(!xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(&vtd_drhd[drhd_handle], vtd_ret_addr)){
            _XDPRINTF_("%s: Halting: error in setting DRHD RET\n", __func__);
            HALT();
		}

		//invalidate caches
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(&vtd_drhd[drhd_handle])){
            _XDPRINTF_("%s: Halting: error in invalidating caches\n", __func__);
            HALT();
		}

		//enable VT-d translation
		xmhfhw_platform_x86pc_vtd_drhd_enable_translation(&vtd_drhd[drhd_handle]);

		//disable PMRs now (since DMA protection is active via translation)
		xmhfhw_platform_x86pc_vtd_drhd_disable_pmr(&vtd_drhd[drhd_handle]);

		_XDPRINTF_("%s: Successfully setup DRHD unit %u\n", __func__, drhd_handle);
	}

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	xmhfhw_sysmemaccess_writeu32(vtd_dmar_table_physical_address, 0UL);


    _XDPRINTF_("%s: final page-walk level=%u\n", __func__, vtd_pagewalk_level);

    return vtd_pagewalk_level;
}


static void __xmhfhic_x86vmxx86pc_postdrt(void){
	txt_heap_t *txt_heap;
	os_mle_data_t *os_mle_data;

	txt_heap = get_txt_heap();
	_XDPRINTF_("SL: txt_heap = 0x%08x\n", (u32)txt_heap);
	os_mle_data = get_os_mle_data_start((txt_heap_t*)((u32)txt_heap));
	_XDPRINTF_("SL: os_mle_data = 0x%08x\n", (u32)os_mle_data);

	// restore pre-SENTER MTRRs that were overwritten for SINIT launch
	if(!validate_mtrrs(&(os_mle_data->saved_mtrr_state))) {
		_XDPRINTF_("SECURITY FAILURE: validate_mtrrs() failed.\n");
		HALT();
	}
	_XDPRINTF_("SL: Validated MTRRs\n");

	xmhfhw_cpu_x86_restore_mtrrs(&(os_mle_data->saved_mtrr_state));
    _XDPRINTF_("SL: Restored MTRRs\n");
}


//returns 0xFFFFFFFF on error
static u32 _geec_prime_getslabfordevice(u32 bus, u32 dev, u32 func){
    u32 i;

    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        //for now detect rich guest slab and allocate all platform devices to it
        if(_xmhfhic_common_slab_info_table[i].slab_devices.desc_valid &&
            _xmhfhic_common_slab_info_table[i].slab_devices.numdevices == 0xFFFFFFFFUL)
            return i;
    }

    return 0xFFFFFFFFUL;
}


void xmhfhic_arch_setup_slab_device_allocation(void){
    u32 i, vtd_pagewalk_level;
    u32 b, d, f;
    slab_platformdevices_t ddescs;
    slab_params_t spl;
    xmhfgeec_uapi_slabdevpgtbl_initretcet_params_t *initretcetp =
        (xmhfgeec_uapi_slabdevpgtbl_initretcet_params_t *)spl.in_out_params;
    xmhfgeec_uapi_slabdevpgtbl_initdevpgtbl_params_t *initdevpgtblp =
        (xmhfgeec_uapi_slabdevpgtbl_initdevpgtbl_params_t *)spl.in_out_params;
    xmhfgeec_uapi_slabdevpgtbl_binddevice_params_t *binddevicep =
        (xmhfgeec_uapi_slabdevpgtbl_binddevice_params_t *)spl.in_out_params;


    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABDEVPGTBL;
    spl.cpuid = 0; //XXX: fixme, needs to be BSP id


#if defined (__DRT__)
    //post DRT cleanup first
    __xmhfhic_x86vmxx86pc_postdrt();
#endif	//__DRT__

	//initialize platform bus
	xmhfhw_platform_bus_init();

	//check ACPI subsystem
	{
		ACPI_RSDP rsdp;
		if(!xmhfhw_platform_x86pc_acpi_getRSDP(&rsdp)){
			_XDPRINTF_("%s: ACPI RSDP not found, Halting!\n", __func__);
			HALT();
		}
	}

    //slabdevpgtbl:init
    spl.dst_uapifn = XMHFGEEC_UAPI_SDEVPGTBL_INIT;
    XMHF_SLAB_CALLNEW(&spl);

    //slabdevpgtbl:initretcet
    spl.dst_uapifn = XMHFGEEC_UAPI_SDEVPGTBL_INITRETCET;
    XMHF_SLAB_CALLNEW(&spl);

    //use slabdevpgtbl:initdevpgtbl to initialize all slab device page tables
    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        spl.dst_uapifn = XMHFGEEC_UAPI_SDEVPGTBL_INITDEVPGTBL;
        initdevpgtblp->dst_slabid = i;
        XMHF_SLAB_CALLNEW(&spl);
    }
    _XDPRINTF_("%s: initialized slab device page tables\n", __func__);

    //intialize VT-d subsystem and obtain
    vtd_pagewalk_level = _geec_prime_vtd_initialize(initretcetp->result_retpaddr);
    _XDPRINTF_("%s: setup vt-d, page-walk level=%u\n", __func__, vtd_pagewalk_level);


    //enumerate PCI bus to find out all the devices
	//bus numbers range from 0-255, device from 0-31 and function from 0-7
	for(b=0; b < PCI_BUS_MAX; b++){
		for(d=0; d < PCI_DEVICE_MAX; d++){
			for(f=0; f < PCI_FUNCTION_MAX; f++){
				u32 vendor_id, device_id;

				//read device and vendor ids, if no device then both will be 0xFFFF
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_VENDOR_ID, sizeof(u16), &vendor_id);
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_DEVICE_ID, sizeof(u16), &device_id);
				if(vendor_id == 0xFFFF && device_id == 0xFFFF)
					break;

                spl.dst_uapifn = XMHFGEEC_UAPI_SDEVPGTBL_BINDDEVICE;
                binddevicep->dst_slabid = _geec_prime_getslabfordevice(b, d, f);
                if(binddevicep->dst_slabid == 0xFFFFFFFFUL){
                    _XDPRINTF_("%s: Warning, could not find slab for device, skipping\n", __func__);
                    //HALT();
                }else{
                    binddevicep->bus = b;
                    binddevicep->dev = d;
                    binddevicep->func = f;
                    binddevicep->pagewalk_level = vtd_pagewalk_level;
                    XMHF_SLAB_CALLNEW(&spl);
                    _XDPRINTF_("  Allocated device %x:%x:%x(%x:%x) to slab %u\n",
                           b, d, f, vendor_id, device_id, binddevicep->dst_slabid);
                }
			}
		}
	}

}



















//////////////////////////////////////////////////////////////////////////////
// setup slab memory page tables (smt)

#define _SLAB_SPATYPE_MASK_SAMESLAB             (0x100)

#define	_SLAB_SPATYPE_SLAB_CODE					(0x0)
#define	_SLAB_SPATYPE_SLAB_DATA	    			(0x1)
#define _SLAB_SPATYPE_SLAB_STACK				(0x2)
#define _SLAB_SPATYPE_SLAB_DMADATA				(0x3)
#define _SLAB_SPATYPE_SLAB_MMIO 				(0x4)
#define _SLAB_SPATYPE_OTHER	    				(0x5)


static u32 _geec_prime_slab_getspatype(u32 slab_index, u32 spa){
	u32 i;

	//slab memory regions
	for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
		u32 mask = _xmhfhic_common_slab_info_table[i].slabtype;

        if( i == slab_index)
            mask |= _SLAB_SPATYPE_MASK_SAMESLAB;

		if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_end)
			return _SLAB_SPATYPE_SLAB_CODE | mask;
		if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[1].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[1].addr_end)
			return _SLAB_SPATYPE_SLAB_DATA | mask;
		if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_end)
			return _SLAB_SPATYPE_SLAB_STACK | mask;
		if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_end)
			return _SLAB_SPATYPE_SLAB_DMADATA | mask;
		if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[4].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[4].addr_end)
			return _SLAB_SPATYPE_SLAB_MMIO | mask;
	}

	return _SLAB_SPATYPE_OTHER;
}



// for VfT_PROG, uVT_PROG and uVU_PROG
static u64 _geec_prime_slab_getptflagsforspa_pae(u32 slabid, u32 spa){
	u64 flags=0;
    u8 spa_slabtype, spa_slabregion;
    bool spa_sameslab=false;
	u32 spatype = _geec_prime_slab_getspatype(slabid, spa);
	//_XDPRINTF_("\n%s: slab_index=%u, spa=%08x, spatype = %x\n", __func__, slab_index, spa, spatype);
    u32 slabtype = _xmhfhic_common_slab_info_table[slabid].slabtype;

    spa_slabregion = spatype & 0x0000000FUL;
    spa_slabtype =spatype & 0x000000F0UL;
    if(spatype & _SLAB_SPATYPE_MASK_SAMESLAB)
        spa_sameslab = true;


    switch(slabtype){
        case XMHFGEEC_SLABTYPE_uVT_PROG:
        case XMHFGEEC_SLABTYPE_uVU_PROG:{
            //self slab: code=rx, data,stack,dmadata=rw, perms=USER
            //other slab vft: code=rx, data,stack,dmadata=rw, perms=SUPER
            //SPATYPE_OTHER => rw perms=USER
            //anything else: unmapped
            if(spa_slabregion == _SLAB_SPATYPE_OTHER){
                flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER);
                if(spa == 0xfee00000 || spa == 0xfec00000) {
                    //map some MMIO regions with Page Cache disabled
                    //0xfed00000 contains Intel TXT config regs & TPM MMIO
                    //0xfee00000 contains LAPIC base
                    flags |= (u64)(_PAGE_PCD);
                }
            }else{
                if(spa_sameslab || spa_slabtype == XMHFGEEC_SLABTYPE_VfT_PROG ||
                    spa_slabtype == XMHFGEEC_SLABTYPE_VfT_SENTINEL){
                    switch(spa_slabregion){
                        case _SLAB_SPATYPE_SLAB_CODE:
                            flags = (_PAGE_PRESENT);
                            break;
                        case _SLAB_SPATYPE_SLAB_DATA:
                        case _SLAB_SPATYPE_SLAB_STACK:
                        case _SLAB_SPATYPE_SLAB_DMADATA:
                            flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX);
                            break;
                        default:
                            flags = 0;
                            break;
                    }

                    if(spa_sameslab)
                        flags |= (_PAGE_USER);

                }else{
                    flags =0;
                }

            }
        }
        break;



        case XMHFGEEC_SLABTYPE_VfT_PROG:{
            //self slab: code=rx, data,stack,dmadata=rw, perms=SUPER
            //other slab vft: code=rx, data,stack,dmadata=rw, perms=SUPER
            //SPATYPE_OTHER => rw perms=USER
            //anything else: mapped rw perms=USER
            if(spa_slabregion == _SLAB_SPATYPE_OTHER){
                flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER);
                if(spa == 0xfee00000 || spa == 0xfec00000) {
                    //map some MMIO regions with Page Cache disabled
                    //0xfed00000 contains Intel TXT config regs & TPM MMIO
                    //0xfee00000 contains LAPIC base
                    flags |= (u64)(_PAGE_PCD);
                }
            }else{
                if(spa_sameslab || spa_slabtype == XMHFGEEC_SLABTYPE_VfT_PROG ||
                    spa_slabtype == XMHFGEEC_SLABTYPE_VfT_SENTINEL){
                    switch(spa_slabregion){
                        case _SLAB_SPATYPE_SLAB_CODE:
                            flags = (_PAGE_PRESENT);
                            break;
                        case _SLAB_SPATYPE_SLAB_DATA:
                        case _SLAB_SPATYPE_SLAB_STACK:
                        case _SLAB_SPATYPE_SLAB_DMADATA:
                            flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX);
                            break;
                        default:
                            flags = 0;
                            break;
                    }

                }else{
                    flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX | _PAGE_USER);
                }

            }

        }
        break;

        default:
            _XDPRINTF_("%s: invalid slab type=%x. Halting!\n", __func__,
                       slabtype);
            HALT();

    }

    return flags;
}




// only for uVU_PROG_GUEST, uVU_PROG_RICHGUEST and uVT_PROG_GUEST
static u64 _geec_prime_slab_getptflagsforspa_ept(u32 slabid, u32 spa){
	u64 flags=0;
    u8 spa_slabtype, spa_slabregion;
    bool spa_sameslab=false;
	u32 spatype = _geec_prime_slab_getspatype(slabid, spa);
	//_XDPRINTF_("\n%s: slab_index=%u, spa=%08x, spatype = %x\n", __func__, slab_index, spa, spatype);
    u32 slabtype = _xmhfhic_common_slab_info_table[slabid].slabtype;

    spa_slabregion = spatype & 0x0000000FUL;
    spa_slabtype =spatype & 0x000000F0UL;
    if(spatype & _SLAB_SPATYPE_MASK_SAMESLAB)
        spa_sameslab = true;


    switch(slabtype){

        case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
        case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:{
            //code=rx, data,stack,dmadata=rw;
            //other slabs = no mapping; other region = no mapping
            if(spa_sameslab && spa_slabregion != _SLAB_SPATYPE_OTHER){
                switch(spa_slabregion){
                    case _SLAB_SPATYPE_SLAB_CODE:
                        flags = 0x5;
                        break;
                    case _SLAB_SPATYPE_SLAB_DATA:
                    case _SLAB_SPATYPE_SLAB_STACK:
                    case _SLAB_SPATYPE_SLAB_DMADATA:
                    case _SLAB_SPATYPE_SLAB_MMIO:
                        flags = 0x3;
                        break;
                }
            }else{
                flags=0;
            }
        }
        break;

        case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
            //code,data,stack,dmadata,mmio=rwx;
            //other slabs = no mapping; other region = rwx
            if(spa_sameslab || spa_slabregion == _SLAB_SPATYPE_OTHER)
                flags = 0x7;
            else
                flags = 0;
        }
        break;

        default:
            _XDPRINTF_("%s: invalid slab type=%x. Halting!\n", __func__,
                       slabtype);
            HALT();
    }

    return flags;

}


static struct _memorytype _vmx_ept_memorytypes[MAX_MEMORYTYPE_ENTRIES]; //EPT memory types array


//---gather memory types for system physical memory------------------------------
static void __xmhfhic_vmx_gathermemorytypes(void){
 	u32 eax, ebx, ecx, edx;
	u32 index=0;
	u32 num_vmtrrs=0;	//number of variable length MTRRs supported by the CPU

	//0. sanity check
  	//check MTRR support
  	eax=0x00000001;
  	ecx=0x00000000;
    CASM_FUNCCALL(xmhfhw_cpu_cpuid,0x00000001, &eax, &ebx, &ecx, &edx);

  	if( !(edx & (u32)(1 << 12)) ){
  		_XDPRINTF_("\n%s: CPU does not support MTRRs!", __func__);
  		HALT();
  	}

  	//check MTRR caps
  	rdmsr(IA32_MTRRCAP, &eax, &edx);
	num_vmtrrs = (u8)eax;
  	_XDPRINTF_("\nIA32_MTRRCAP: VCNT=%u, FIX=%u, WC=%u, SMRR=%u",
  		num_vmtrrs, ((eax & (1 << 8)) >> 8),  ((eax & (1 << 10)) >> 10),
  			((eax & (1 << 11)) >> 11));
	//sanity check that fixed MTRRs are supported
  	HALT_ON_ERRORCOND( ((eax & (1 << 8)) >> 8) );
  	//ensure number of variable MTRRs are within the maximum supported
  	HALT_ON_ERRORCOND( (num_vmtrrs <= MAX_VARIABLE_MEMORYTYPE_ENTRIES) );


	#ifndef __XMHF_VERIFICATION__
	//1. clear memorytypes array
	memset((void *)&_vmx_ept_memorytypes, 0, sizeof(struct _memorytype) * MAX_MEMORYTYPE_ENTRIES);
	#endif

	//2. grab memory types using FIXED MTRRs
    //0x00000000-0x0007FFFF
    rdmsr(IA32_MTRR_FIX64K_00000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x00000000; _vmx_ept_memorytypes[index].endaddr = 0x0000FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x00010000; _vmx_ept_memorytypes[index].endaddr = 0x0001FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x00020000; _vmx_ept_memorytypes[index].endaddr = 0x0002FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x00030000; _vmx_ept_memorytypes[index].endaddr = 0x0003FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x00040000; _vmx_ept_memorytypes[index].endaddr = 0x0004FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x00050000; _vmx_ept_memorytypes[index].endaddr = 0x0005FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x00060000; _vmx_ept_memorytypes[index].endaddr = 0x0006FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x00070000; _vmx_ept_memorytypes[index].endaddr = 0x0007FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x00080000-0x0009FFFF
  	rdmsr(IA32_MTRR_FIX16K_80000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x00080000; _vmx_ept_memorytypes[index].endaddr = 0x00083FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x00084000; _vmx_ept_memorytypes[index].endaddr = 0x00087FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x00088000; _vmx_ept_memorytypes[index].endaddr = 0x0008BFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x0008C000; _vmx_ept_memorytypes[index].endaddr = 0x0008FFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x00090000; _vmx_ept_memorytypes[index].endaddr = 0x00093FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x00094000; _vmx_ept_memorytypes[index].endaddr = 0x00097FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x00098000; _vmx_ept_memorytypes[index].endaddr = 0x0009BFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x0009C000; _vmx_ept_memorytypes[index].endaddr = 0x0009FFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000A0000-0x000BFFFF
	  rdmsr(IA32_MTRR_FIX16K_A0000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000A0000; _vmx_ept_memorytypes[index].endaddr = 0x000A3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000A4000; _vmx_ept_memorytypes[index].endaddr = 0x000A7FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000A8000; _vmx_ept_memorytypes[index].endaddr = 0x000ABFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000AC000; _vmx_ept_memorytypes[index].endaddr = 0x000AFFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000B0000; _vmx_ept_memorytypes[index].endaddr = 0x000B3FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000B4000; _vmx_ept_memorytypes[index].endaddr = 0x000B7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000B8000; _vmx_ept_memorytypes[index].endaddr = 0x000BBFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000BC000; _vmx_ept_memorytypes[index].endaddr = 0x000BFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000C0000-0x000C7FFF
    rdmsr(IA32_MTRR_FIX4K_C0000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000C0000; _vmx_ept_memorytypes[index].endaddr = 0x000C0FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000C1000; _vmx_ept_memorytypes[index].endaddr = 0x000C1FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000C2000; _vmx_ept_memorytypes[index].endaddr = 0x000C2FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000C3000; _vmx_ept_memorytypes[index].endaddr = 0x000C3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000C4000; _vmx_ept_memorytypes[index].endaddr = 0x000C4FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000C5000; _vmx_ept_memorytypes[index].endaddr = 0x000C5FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000C6000; _vmx_ept_memorytypes[index].endaddr = 0x000C6FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000C7000; _vmx_ept_memorytypes[index].endaddr = 0x000C7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000C8000-0x000C8FFF
	  rdmsr(IA32_MTRR_FIX4K_C8000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000C8000; _vmx_ept_memorytypes[index].endaddr = 0x000C8FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000C9000; _vmx_ept_memorytypes[index].endaddr = 0x000C9FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000CA000; _vmx_ept_memorytypes[index].endaddr = 0x000CAFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000CB000; _vmx_ept_memorytypes[index].endaddr = 0x000CBFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000CC000; _vmx_ept_memorytypes[index].endaddr = 0x000CCFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000CD000; _vmx_ept_memorytypes[index].endaddr = 0x000CDFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000CE000; _vmx_ept_memorytypes[index].endaddr = 0x000CEFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000CF000; _vmx_ept_memorytypes[index].endaddr = 0x000CFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000D0000-0x000D7FFF
    rdmsr(IA32_MTRR_FIX4K_D0000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000D0000; _vmx_ept_memorytypes[index].endaddr = 0x000D0FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000D1000; _vmx_ept_memorytypes[index].endaddr = 0x000D1FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000D2000; _vmx_ept_memorytypes[index].endaddr = 0x000D2FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000D3000; _vmx_ept_memorytypes[index].endaddr = 0x000D3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000D4000; _vmx_ept_memorytypes[index].endaddr = 0x000D4FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000D5000; _vmx_ept_memorytypes[index].endaddr = 0x000D5FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000D6000; _vmx_ept_memorytypes[index].endaddr = 0x000D6FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000D7000; _vmx_ept_memorytypes[index].endaddr = 0x000D7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000D8000-0x000DFFFF
  	rdmsr(IA32_MTRR_FIX4K_D8000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000D8000; _vmx_ept_memorytypes[index].endaddr = 0x000D8FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000D9000; _vmx_ept_memorytypes[index].endaddr = 0x000D9FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000DA000; _vmx_ept_memorytypes[index].endaddr = 0x000DAFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000DB000; _vmx_ept_memorytypes[index].endaddr = 0x000DBFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000DC000; _vmx_ept_memorytypes[index].endaddr = 0x000DCFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000DD000; _vmx_ept_memorytypes[index].endaddr = 0x000DDFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000DE000; _vmx_ept_memorytypes[index].endaddr = 0x000DEFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000DF000; _vmx_ept_memorytypes[index].endaddr = 0x000DFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000E0000-0x000E7FFF
    rdmsr(IA32_MTRR_FIX4K_E0000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000E0000; _vmx_ept_memorytypes[index].endaddr = 0x000E0FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000E1000; _vmx_ept_memorytypes[index].endaddr = 0x000E1FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000E2000; _vmx_ept_memorytypes[index].endaddr = 0x000E2FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000E3000; _vmx_ept_memorytypes[index].endaddr = 0x000E3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000E4000; _vmx_ept_memorytypes[index].endaddr = 0x000E4FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000E5000; _vmx_ept_memorytypes[index].endaddr = 0x000E5FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000E6000; _vmx_ept_memorytypes[index].endaddr = 0x000E6FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000E7000; _vmx_ept_memorytypes[index].endaddr = 0x000E7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000E8000-0x000EFFFF
	  rdmsr(IA32_MTRR_FIX4K_E8000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000E8000; _vmx_ept_memorytypes[index].endaddr = 0x000E8FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000E9000; _vmx_ept_memorytypes[index].endaddr = 0x000E9FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000EA000; _vmx_ept_memorytypes[index].endaddr = 0x000EAFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000EB000; _vmx_ept_memorytypes[index].endaddr = 0x000EBFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000EC000; _vmx_ept_memorytypes[index].endaddr = 0x000ECFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000ED000; _vmx_ept_memorytypes[index].endaddr = 0x000EDFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000EE000; _vmx_ept_memorytypes[index].endaddr = 0x000EEFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000EF000; _vmx_ept_memorytypes[index].endaddr = 0x000EFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000F0000-0x000F7FFF
  	rdmsr(IA32_MTRR_FIX4K_F0000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000F0000; _vmx_ept_memorytypes[index].endaddr = 0x000F0FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000F1000; _vmx_ept_memorytypes[index].endaddr = 0x000F1FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000F2000; _vmx_ept_memorytypes[index].endaddr = 0x000F2FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000F3000; _vmx_ept_memorytypes[index].endaddr = 0x000F3FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000F4000; _vmx_ept_memorytypes[index].endaddr = 0x000F4FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000F5000; _vmx_ept_memorytypes[index].endaddr = 0x000F5FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000F6000; _vmx_ept_memorytypes[index].endaddr = 0x000F6FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000F7000; _vmx_ept_memorytypes[index].endaddr = 0x000F7FFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);
    //0x000F8000-0x000FFFFF
  	rdmsr(IA32_MTRR_FIX4K_F8000, &eax, &edx);
    _vmx_ept_memorytypes[index].startaddr = 0x000F8000; _vmx_ept_memorytypes[index].endaddr = 0x000F8FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000F9000; _vmx_ept_memorytypes[index].endaddr = 0x000F9FFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000FA000; _vmx_ept_memorytypes[index].endaddr = 0x000FAFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000FB000; _vmx_ept_memorytypes[index].endaddr = 0x000FBFFF; _vmx_ept_memorytypes[index++].type= ((eax & 0xFF000000) >> 24);
    _vmx_ept_memorytypes[index].startaddr = 0x000FC000; _vmx_ept_memorytypes[index].endaddr = 0x000FCFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x000000FF) >> 0);
    _vmx_ept_memorytypes[index].startaddr = 0x000FD000; _vmx_ept_memorytypes[index].endaddr = 0x000FDFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x0000FF00) >> 8);
    _vmx_ept_memorytypes[index].startaddr = 0x000FE000; _vmx_ept_memorytypes[index].endaddr = 0x000FEFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0x00FF0000) >> 16);
    _vmx_ept_memorytypes[index].startaddr = 0x000FF000; _vmx_ept_memorytypes[index].endaddr = 0x000FFFFF; _vmx_ept_memorytypes[index++].type= ((edx & 0xFF000000) >> 24);


	//3. grab memory types using variable length MTRRs
	{
		u64 paddrmask = 0x0000000FFFFFFFFFULL; //36-bits physical address, TODO: need to make this dynamic
		u64 vMTRR_base, vMTRR_mask;
		u32 msrval=IA32_MTRR_PHYSBASE0;
		u32 i;

		for(i=0; i < num_vmtrrs; i++){
			rdmsr(msrval, &eax, &edx);
			vMTRR_base = ((u64)edx << 32) | (u64)eax;
			msrval++;
			rdmsr(msrval, &eax, &edx);
			vMTRR_mask = ((u64)edx << 32) | (u64)eax;
			msrval++;
			if( (vMTRR_mask & ((u64)1 << 11)) ){
				_vmx_ept_memorytypes[index].startaddr = (vMTRR_base & (u64)0xFFFFFFFFFFFFF000ULL);
				_vmx_ept_memorytypes[index].endaddr = (vMTRR_base & (u64)0xFFFFFFFFFFFFF000ULL) +
					(u64) (~(vMTRR_mask & (u64)0xFFFFFFFFFFFFF000ULL) &
						paddrmask);
				_vmx_ept_memorytypes[index++].type = ((u32)vMTRR_base & (u32)0x000000FF);
			}else{
				_vmx_ept_memorytypes[index++].invalid = 1;
			}
		}
	}

	_XDPRINTF_("\n%s: gathered MTRR details, number of entries=%u", __func__, index);
	HALT_ON_ERRORCOND( index <= (MAX_MEMORYTYPE_ENTRIES+1) );

  //[debug: dump the contents of _vmx_ept_memorytypes]
  //{
  //  int i;
  //  for(i=0; i < MAX_MEMORYTYPE_ENTRIES; i++){
  //    _XDPRINTF_("\nrange  0x%016llx-0x%016llx (type=%u)",
  //      _vmx_ept_memorytypes[i].startaddr, _vmx_ept_memorytypes[i].endaddr, _vmx_ept_memorytypes[i].type);
  //  }
  //}


}


//---get memory type for a given physical page address--------------------------
//
//11.11.4.1 MTRR Precedences
//  0. if MTRRs are not enabled --> MTRR_TYPE_UC
//  if enabled then
     //if physaddr < 1MB use fixed MTRR ranges return type
     //else if within a valid variable range MTRR then
        //if a single match, return type
        //if two or more and one is UC, return UC
        //if two or more and WB and WT, return WT
        //else invalid combination
     //else
       // return default memory type
//
static u32 _geec_prime_vmx_getmemorytypeforphysicalpage(u64 pagebaseaddr){
 int i;
 u32 prev_type= MTRR_TYPE_RESV;

  //check if page base address under 1M, if so used FIXED MTRRs
  if(pagebaseaddr < (1024*1024)){
    for(i=0; i < MAX_FIXED_MEMORYTYPE_ENTRIES; i++){
      if( pagebaseaddr >= _vmx_ept_memorytypes[i].startaddr && (pagebaseaddr+PAGE_SIZE_4K-1) <= _vmx_ept_memorytypes[i].endaddr )
        return _vmx_ept_memorytypes[i].type;
    }

    _XDPRINTF_("\n%s: endaddr < 1M and unmatched fixed MTRR. Halt!", __func__);
    HALT();
  }

  //page base address is above 1M, use VARIABLE MTRRs
  for(i= MAX_FIXED_MEMORYTYPE_ENTRIES; i < MAX_MEMORYTYPE_ENTRIES; i++){
    if( pagebaseaddr >= _vmx_ept_memorytypes[i].startaddr && (pagebaseaddr+PAGE_SIZE_4K-1) <= _vmx_ept_memorytypes[i].endaddr &&
          (!_vmx_ept_memorytypes[i].invalid) ){
       if(_vmx_ept_memorytypes[i].type == MTRR_TYPE_UC){
        prev_type = MTRR_TYPE_UC;
       }else if(_vmx_ept_memorytypes[i].type == MTRR_TYPE_WT && prev_type != MTRR_TYPE_UC){
        prev_type = MTRR_TYPE_WT;
       }else{
        if(prev_type != MTRR_TYPE_UC && prev_type != MTRR_TYPE_WT){
          if(prev_type == MTRR_TYPE_RESV){
            prev_type = _vmx_ept_memorytypes[i].type;
          }else{
            _XDPRINTF_("\nprev_type=%u, _vmx_ept_memorytypes=%u", prev_type, _vmx_ept_memorytypes[i].type);
            HALT_ON_ERRORCOND ( prev_type == _vmx_ept_memorytypes[i].type);
          }
        }
       }
    }
  }

  if(prev_type == MTRR_TYPE_RESV)
    prev_type = MTRR_TYPE_WB; //todo: need to dynamically get the default MTRR (usually WB)

  return prev_type;
}


static void _geec_prime_populate_slab_pagetables_VfT_prog(u32 slabid){
	u64 gpa;
	u64 flags;
    slab_params_t spl;
    xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;

    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
    spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid

	for(gpa=0; gpa < ADDR_4GB; gpa += PAGE_SIZE_2M){
        flags = _geec_prime_slab_getptflagsforspa_pae(slabid, (u32)gpa);

        spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = slabid;
        setentryforpaddrp->gpa = gpa;
        setentryforpaddrp->entry = pae_make_pde_big(gpa, flags);
        XMHF_SLAB_CALLNEW(&spl);

	}


}



static void _geec_prime_populate_slab_pagetables_uVT_uVU_prog(u32 slabid){
	u64 gpa;
	u64 flags;
    slab_params_t spl;
    u32 i;
    u32 spatype;
    bool spa_sameslab=false;
    xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;

    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
    spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid



	for(gpa=0; gpa < ADDR_4GB; gpa += PAGE_SIZE_2M){
        spatype = _geec_prime_slab_getspatype(slabid, gpa);
        if(spatype & _SLAB_SPATYPE_MASK_SAMESLAB)
            spa_sameslab = true;
        else
            spa_sameslab = false;

        flags = _geec_prime_slab_getptflagsforspa_pae(slabid, (u32)gpa);
        if(spa_sameslab){
            flags |= (_PAGE_USER);
            _XDPRINTF_("%s: setting USER for addr=%x in slab=%u, flags=%016llx\n", __func__,
                       (u32)gpa, slabid, flags);
        }
        spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = slabid;
        setentryforpaddrp->gpa = gpa;
        setentryforpaddrp->entry = pae_make_pde_big(gpa, flags);
        XMHF_SLAB_CALLNEW(&spl);

	}


}





static void _geec_prime_populate_slab_pagetables_uVT_uVU_prog_guest(u32 slabid){
	u64 p_table_value;
	u64 gpa;
	u64 flags;
    slab_params_t spl;
    xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;

    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
    spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid

/*    _XDPRINTF_("%s: mapping guest prog 2M slab %u...\n", __func__,
               slabid);
    _XDPRINTF_("%s: mapping %x-%x\n", __func__,
               _xmhfhic_common_slab_info_table[slabid].slab_physmem_extents[0].addr_start,
               _xmhfhic_common_slab_info_table[slabid].slab_physmem_extents[4].addr_end);
*/

    //code=rx, 2M mapping
    for(gpa = _xmhfhic_common_slab_info_table[slabid].slab_physmem_extents[0].addr_start;
        gpa < _xmhfhic_common_slab_info_table[slabid].slab_physmem_extents[0].addr_end;
        gpa += PAGE_SIZE_2M){
		u32 memorytype = _geec_prime_vmx_getmemorytypeforphysicalpage((u64)gpa);
        flags = 0x85;

        if(memorytype == 0)
            p_table_value = (u64) (gpa)  | ((u64)memorytype << 3) |  flags ;	//present, UC
        else
            p_table_value = (u64) (gpa)  | ((u64)6 << 3) | flags ;	//present, WB, track host MTRR

        spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = slabid;
        setentryforpaddrp->gpa = gpa;
        setentryforpaddrp->entry = p_table_value;
        XMHF_SLAB_CALLNEW(&spl);
    }

    //data,stack,dmadata=rw, 2M mapping
    for(gpa = _xmhfhic_common_slab_info_table[slabid].slab_physmem_extents[1].addr_start;
        gpa < _xmhfhic_common_slab_info_table[slabid].slab_physmem_extents[3].addr_end;
        gpa += PAGE_SIZE_2M){
		u32 memorytype = _geec_prime_vmx_getmemorytypeforphysicalpage((u64)gpa);
        flags = 0x83;

        if(memorytype == 0)
            p_table_value = (u64) (gpa)  | ((u64)memorytype << 3) |  flags ;	//present, UC
        else
            p_table_value = (u64) (gpa)  | ((u64)6 << 3) | flags ;	//present, WB, track host MTRR

        spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = slabid;
        setentryforpaddrp->gpa = gpa;
        setentryforpaddrp->entry = p_table_value;
        XMHF_SLAB_CALLNEW(&spl);
    }


#if defined (__DEBUG_SERIAL__)
        spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = slabid;
        setentryforpaddrp->gpa = ADDR_LIBXMHFDEBUGDATA;
        p_table_value = (u64) (ADDR_LIBXMHFDEBUGDATA)  | ((u64)6 << 3) | 0x87 ;	//present, WB, track host MTRR
        setentryforpaddrp->entry = p_table_value;
        XMHF_SLAB_CALLNEW(&spl);
#endif

}


//ept4k
static void _geec_prime_populate_slab_pagetables_ept4k(u32 slabid){
	u64 p_table_value;
	u64 gpa;
	u64 flags;
    slab_params_t spl;
    xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;

    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
    spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid

	for(gpa=0; gpa < ADDR_4GB; gpa += PAGE_SIZE_4K){
		u32 memorytype = _geec_prime_vmx_getmemorytypeforphysicalpage((u64)gpa);
        flags = _geec_prime_slab_getptflagsforspa_ept(slabid, (u32)gpa);

        if(memorytype == 0)
            p_table_value = (u64) (gpa)  | ((u64)memorytype << 3) |  flags ;	//present, UC
        else
            p_table_value = (u64) (gpa)  | ((u64)6 << 3) | flags ;	//present, WB, track host MTRR

        spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = slabid;
        setentryforpaddrp->gpa = gpa;
        setentryforpaddrp->entry = p_table_value;
        XMHF_SLAB_CALLNEW(&spl);

	}

#if defined (__DEBUG_SERIAL__)
        spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = slabid;
        setentryforpaddrp->gpa = ADDR_LIBXMHFDEBUGDATA;
        p_table_value = (u64) (ADDR_LIBXMHFDEBUGDATA)  | ((u64)6 << 3) | 0x7 ;	//present, WB, track host MTRR
        setentryforpaddrp->entry = p_table_value;
        XMHF_SLAB_CALLNEW(&spl);
#endif


}

//pae4k
static void _geec_prime_populate_slab_pagetables_pae4k(u32 slabid){
	u64 gpa;
	u64 flags;
    slab_params_t spl;
    xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;

    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
    spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid

	for(gpa=0; gpa < ADDR_4GB; gpa += PAGE_SIZE_4K){
        flags = _geec_prime_slab_getptflagsforspa_pae(slabid, (u32)gpa);
        //_XDPRINTF_("gpa=%08x, flags=%016llx\n", (u32)gpa, flags);

        spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = slabid;
        setentryforpaddrp->gpa = gpa;
        setentryforpaddrp->entry = pae_make_pte(gpa, flags);
        XMHF_SLAB_CALLNEW(&spl);

	}

#if defined (__DEBUG_SERIAL__)
        spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = slabid;
        setentryforpaddrp->gpa = ADDR_LIBXMHFDEBUGDATA;
        setentryforpaddrp->entry = pae_make_pte(ADDR_LIBXMHFDEBUGDATA, (_PAGE_USER | _PAGE_RW | _PAGE_PRESENT));	//present, WB, track host MTRR
        XMHF_SLAB_CALLNEW(&spl);
#endif


}

void xmhfhic_arch_setup_slab_mem_page_tables(void){
    slab_params_t spl;
    xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *initmempgtblp =
        (xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *)spl.in_out_params;
    u32 i, slabtype;

    _XDPRINTF_("%s: starting...\n", __func__);

    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
    spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid here

    //gather memory types for EPT (for guest slabs)
    __xmhfhic_vmx_gathermemorytypes();
    _XDPRINTF_("%s: gathered EPT memory types\n", __func__);


    //setup verified slabs' page tables, uses slab index for GEEC_PRIME
    spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL;
    initmempgtblp->dst_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    XMHF_SLAB_CALLNEW(&spl);
    _geec_prime_populate_slab_pagetables_pae4k(XMHFGEEC_SLAB_GEEC_PRIME);
   	_XDPRINTF_("%s: populated verified slabs' memory page tables\n", __func__);


    //setup unverified slabs's page tables
    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        slabtype = _xmhfhic_common_slab_info_table[i].slabtype;

        switch(slabtype){
            case XMHFGEEC_SLABTYPE_uVT_PROG:
            case XMHFGEEC_SLABTYPE_uVU_PROG:{
                spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL;
                initmempgtblp->dst_slabid = i;
                XMHF_SLAB_CALLNEW(&spl);
                _geec_prime_populate_slab_pagetables_pae4k(i);
              	_XDPRINTF_("%s: slab %u --> uV{T,U}_prog page-tables populated\n", __func__, i);
            }
            break;


            case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
            case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:
            case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
                spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL;
                initmempgtblp->dst_slabid = i;
                XMHF_SLAB_CALLNEW(&spl);
                _geec_prime_populate_slab_pagetables_ept4k(i);
              	_XDPRINTF_("%s: slab %u --> uV{T,U}_prog_guest page-tables populated\n", __func__, i);
            }
            break;

            default:
                break;
        }
    }


	_XDPRINTF_("%s: setup slab memory page tables\n", __func__);
    //_XDPRINTF_("%s: wip. halting!\n");
    //HALT();
}


















































































#if 0

    //debug
    _XDPRINTF_("Halting!\n");
    _XDPRINTF_("XMHF Tester Finished!\n");
    HALT();

#endif // 0
