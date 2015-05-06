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
#include <uapi_slabiotbl.h>
#include <xc_init.h>

__attribute__((aligned(4096))) static u64 _xcprimeon_init_pdt[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
__attribute__((aligned(4096))) static u64 _xcprimeon_init_pdpt[PAE_MAXPTRS_PER_PDPT];
static u64 _xcsmp_ap_entry_lock = 1;
static mtrr_state_t _mtrrs;
static u64 _ap_cr3=0;

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


    //setup (unverified) slab iotbl
    geec_prime_setup_slab_iotbl();


    //setup slab memory page tables
    xmhfhic_arch_setup_slab_mem_page_tables();
#endif //__XMHF_VERIFICATION__

    //switch to prime page tables
    _XDPRINTF_("Proceeding to switch to GEEC_PRIME pagetables...\n");
    CASM_FUNCCALL(write_cr3,(u32)_xmhfhic_common_slab_info_table[XMHFGEEC_SLAB_GEEC_PRIME].mempgtbl_cr3);
    _XDPRINTF_("Switched to GEEC_PRIME pagetables...\n");

/*    //transfer control to geec_primesmp
    {
        slab_params_t spl;
        spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
        spl.dst_slabid = XMHFGEEC_SLAB_GEEC_PRIMESMP;
        spl.dst_uapifn = 0;
        spl.cpuid = 0;
        XMHF_SLAB_CALLNEW(&spl);
    }*/

    //setup (SMP) CPU state
    _geec_prime_setup_cpustate();

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
			u32 i, j;

			for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
				_XDPRINTF_("slab %u: dumping slab header\n", i);
				_XDPRINTF_("	slabtype=%08x\n", _xmhfhic_common_slab_info_table[i].slabtype);
				_XDPRINTF_("	slab_inuse=%s\n", ( _xmhfhic_common_slab_info_table[i].slab_inuse ? "true" : "false") );
				_XDPRINTF_("	slab_callcaps=%08x\n", _xmhfhic_common_slab_info_table[i].slab_callcaps);
				//_XDPRINTF_("	slab_devices=%s\n", ( _xmhfhic_common_slab_info_table[i].slab_devices.desc_valid ? "true" : "false") );
				_XDPRINTF_("	incl_devices_count=%u\n", _xmhfhic_common_slab_info_table[i].incl_devices_count );
                for(j=0; j < _xmhfhic_common_slab_info_table[i].incl_devices_count; j++)
                        _XDPRINTF_("        vendor_id=%x, device_id=%x\n",
                                   _xmhfhic_common_slab_info_table[i].incl_devices[j].vendor_id,
                                   _xmhfhic_common_slab_info_table[i].incl_devices[j].device_id);
				_XDPRINTF_("	excl_devices_count=%u\n", _xmhfhic_common_slab_info_table[i].excl_devices_count );
                for(j=0; j < _xmhfhic_common_slab_info_table[i].excl_devices_count; j++)
                        _XDPRINTF_("        vendor_id=%x, device_id=%x\n",
                                   _xmhfhic_common_slab_info_table[i].excl_devices[j].vendor_id,
                                   _xmhfhic_common_slab_info_table[i].excl_devices[j].device_id);

				_XDPRINTF_("	slab_pgtblbase=%x\n", ( _xmhfhic_common_slab_info_table[i].mempgtbl_cr3) );
				_XDPRINTF_("	slab_iotblbase=%x\n", ( _xmhfhic_common_slab_info_table[i].iotbl_base) );
				_XDPRINTF_("  slab_code(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_end);
				_XDPRINTF_("  slab_data(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[1].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[1].addr_end);
				_XDPRINTF_("  slab_stack(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_end);
				_XDPRINTF_("  slab_dmadata(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_end);
				_XDPRINTF_("  slab_entrystub=%08x\n", _xmhfhic_common_slab_info_table[i].entrystub);

                /*{
                    u32 j;

                    for(j=0; j < MAX_PLATFORM_CPUS; j++)
                        //_XDPRINTF_("     CPU %u: stack TOS=%016llx\n", j,
                        //       _xmhfhic_common_slab_info_table[i].slabtos[j]);
                        _XDPRINTF_("     CPU %u: stack TOS=%08x\n", j,
                               _xmhfhic_common_slab_info_table[i].slabtos[j]);
                }*/

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
static sysdev_memioregions_t sysdev_memioregions[MAX_PLATFORM_DEVICES];
static u32 numentries_sysdev_memioregions=0;



//DMA Remapping Hardware Unit Definitions
static VTD_DRHD vtd_drhd[VTD_MAX_DRHD];
static u32 vtd_num_drhd=0;	//total number of DMAR h/w units
static bool vtd_drhd_scanned=false;	//set to true once DRHD units have been scanned in the system

static vtd_drhd_handle_t vtd_drhd_maxhandle=0;
static u32 vtd_dmar_table_physical_address=0;


//scan for available DRHD units on the platform and populate the
//global variables set:
//vtd_drhd[] (struct representing a DRHD unit)
//vtd_num_drhd (number of DRHD units detected)
//vtd_dmar_table_physical_address (physical address of the DMAR table)
//returns: true if all is fine else false; dmar_phys_addr_var contains
//max. value of DRHD unit handle (0 through maxhandle-1 are valid handles
//that can subsequently be passed to any of the other vtd drhd functions)
//physical address of the DMAR table in the system
//static bool xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(vtd_drhd_handle_t *maxhandle, u32 *dmar_phys_addr_var){
static bool xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(void){

	ACPI_RSDP rsdp;
	ACPI_RSDT rsdt;
	u32 num_rsdtentries;
	u32 rsdtentries[ACPI_MAX_RSDT_ENTRIES];
	u32 status;
	VTD_DMAR dmar;
	u32 i, dmarfound;
	u32 remappingstructuresaddrphys;
	//u32 vtd_dmar_table_physical_address;

	//zero out rsdp and rsdt structures
	//memset(&rsdp, 0, sizeof(ACPI_RSDP));
	//memset(&rsdt, 0, sizeof(ACPI_RSDT));

	//set maxhandle to 0 to start with. if we have any errors before
	//we finalize maxhandle we can just bail out
	vtd_drhd_maxhandle=0;

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
	//*dmar_phys_addr_var = vtd_dmar_table_physical_address; //store it in supplied argument
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

	vtd_drhd_maxhandle = vtd_num_drhd;
	vtd_drhd_scanned = true;

	return true;
}


static void _sda_enumerate_system_devices(void){
    u32 b, d, f, i;
	vtd_drhd_handle_t drhd_handle;



    //as a first step, add several non-PCI system devices to the
    //sysdev list using XMHF/GEEC psuedo-PCI vendor and device IDs
    //the following are the list of non-PCI system devices:
    //LAPIC at X86SMP_LAPIC_MEMORYADDRESS (0xFEE00000)
    //TPM at TPM_LOCALITY_BASE (0xfed40000)
    //TXT at TXT_PUB_CONFIG_REGS_BASE (0xfed30000) and TXT_PRIV_CONFIG_REGS_BASE (0xfed20000)
    //IOMMU as described by vtd_drhd[]


    //sanity check available sysdev entries for the above devices
    if( (numentries_sysdev_memioregions+vtd_drhd_maxhandle+1+1+1) >= MAX_PLATFORM_DEVICES){
        _XDPRINTF_("%s: Halting!. numentries_sysdev_memioregions >= MAX_PLATFORM_DEVICES(%u)\n",
                   __func__, MAX_PLATFORM_DEVICES);
        HALT();
    }

    //add LAPIC device
    sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].f=0;
    sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_LAPIC;
    sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_LAPIC;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=X86SMP_LAPIC_MEMORYADDRESS;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=X86SMP_LAPIC_MEMORYADDRESS + PAGE_SIZE_4K;
    for(i=1; i < PCI_CONF_MAX_BARS; i++){
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
    }
    numentries_sysdev_memioregions++;

    //add TPM
    sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].f=0;
    sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_TPM;
    sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_TPM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=TPM_LOCALITY_BASE;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=TPM_LOCALITY_BASE + PAGE_SIZE_4K;
    for(i=1; i < PCI_CONF_MAX_BARS; i++){
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
    }
    numentries_sysdev_memioregions++;

    //add TXT
    sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].f=0;
    sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
    sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_TXT;
    sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_TXT;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=TXT_PRIV_CONFIG_REGS_BASE;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=TXT_PRIV_CONFIG_REGS_BASE + PAGE_SIZE_4K;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1].addr_start=TXT_PUB_CONFIG_REGS_BASE;
    sysdev_memioregions[numentries_sysdev_memioregions].memioextents[1].addr_end=TXT_PUB_CONFIG_REGS_BASE + PAGE_SIZE_4K;
    for(i=2; i < PCI_CONF_MAX_BARS; i++){
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
    }
    numentries_sysdev_memioregions++;


    //add IOMMU
	if(!xmhfhw_platform_x86pc_vtd_scanfor_drhd_units()){
        _XDPRINTF_("%s: unable to scan for DRHD units. halting!\n", __func__);
		HALT();
	}

    _XDPRINTF_("%s: Vt-d: maxhandle = %u, dmar table addr=0x%08x\n", __func__,
                (u32)vtd_drhd_maxhandle, (u32)vtd_dmar_table_physical_address);

    for(drhd_handle =0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
        sysdev_memioregions[numentries_sysdev_memioregions].b=PCI_BUS_XMHFGEEC;
        sysdev_memioregions[numentries_sysdev_memioregions].d=PCI_DEVICE_XMHFGEEC;
        sysdev_memioregions[numentries_sysdev_memioregions].f=drhd_handle;
        sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=PCI_VENDOR_ID_XMHFGEEC;
        sysdev_memioregions[numentries_sysdev_memioregions].device_id=PCI_DEVICE_ID_XMHFGEEC_IOMMU;
        sysdev_memioregions[numentries_sysdev_memioregions].dtype = SYSDEV_MEMIOREGIONS_DTYPE_IOMMU;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_start=vtd_drhd[drhd_handle].regbaseaddr;
        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[0].addr_end=vtd_drhd[drhd_handle].regbaseaddr + PAGE_SIZE_4K;
        for(i=1; i < PCI_CONF_MAX_BARS; i++){
            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
        }
        numentries_sysdev_memioregions++;
    }


    //enumerate and add rest of the system devices on the PCI bus
	for(b=0; b < PCI_BUS_MAX; b++){
		for(d=0; d < PCI_DEVICE_MAX; d++){
			for(f=0; f < PCI_FUNCTION_MAX; f++){
				u32 vendor_id, device_id;
				u32 bar_value, i;
				u8 hdr_type;
				u16 command;

				//read device and vendor ids, if no device then both will be 0xFFFF
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_VENDOR_ID, sizeof(u16), &vendor_id);
				xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_DEVICE_ID, sizeof(u16), &device_id);

				if(vendor_id == 0xFFFF && device_id == 0xFFFF)
					break;

                if(numentries_sysdev_memioregions >= MAX_PLATFORM_DEVICES){
                    _XDPRINTF_("%s: Halting!. numentries_sysdev_memioregions >= MAX_PLATFORM_DEVICES(%u)\n",
                               __func__, MAX_PLATFORM_DEVICES);
                    HALT();
                }

                xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_HEADER_TYPE, sizeof(u8), &hdr_type);
                xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(u16), &command);

                //_XDPRINTF_("Device %x:%x:%x(%x:%x) HDR=%x, CMD=%x\n",
                //       b, d, f, vendor_id, device_id, hdr_type, command);
                sysdev_memioregions[numentries_sysdev_memioregions].b=b;
                sysdev_memioregions[numentries_sysdev_memioregions].d=d;
                sysdev_memioregions[numentries_sysdev_memioregions].f=f;
                sysdev_memioregions[numentries_sysdev_memioregions].vendor_id=vendor_id;
                sysdev_memioregions[numentries_sysdev_memioregions].device_id=device_id;

                if(hdr_type == 0x80 || hdr_type == 0x0)
                    sysdev_memioregions[numentries_sysdev_memioregions].dtype=SYSDEV_MEMIOREGIONS_DTYPE_GENERAL;
                else if (hdr_type == 0x81 || hdr_type == 0x1)
                    sysdev_memioregions[numentries_sysdev_memioregions].dtype=SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE;
                else
                    sysdev_memioregions[numentries_sysdev_memioregions].dtype=SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN;

                //disable decode
                xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(u16), (command & ~(0x3)) ) ;


                //size BARs
                for(i=0; i < PCI_CONF_MAX_BARS; i++){
                    if(i >= 2 && (hdr_type == 0x81 || hdr_type == 0x1)){
                        //for PCI-to-PCI bridge devices only BAR0 and BAR1 are valid BARs
                        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
                        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
                        sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
                    }else{
                        //for general devices BAR0-BAR5 are valid BARs
                        u32 bar_size;
                        xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), &bar_value);
                        if(bar_value){
                            if(bar_value & 0x1){ //I/O
                                xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), 0xFFFFFFFFUL);
                                xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), &bar_size);
                                bar_size = bar_size & ~(0x1);
                                bar_size = ~(bar_size);
                                bar_size++;

                                //_XDPRINTF_("  BAR-%u, IO, range=%x to %x\n", i,
                                //           (u16)(bar_value & ~(0x1)), (u16)((bar_value & ~(0x1)) + bar_size) ) ;
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_IO;
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=(u16)(bar_value & ~(0x1));
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=(u16)((bar_value & ~(0x1)) + bar_size);

                           }else{
                                //memory
                                xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), 0xFFFFFFFFUL);
                                xmhf_baseplatform_arch_x86_pci_type1_read(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), &bar_size);
                                bar_size = bar_size & ~(0xF);
                                bar_size = ~(bar_size);
                                bar_size++;

                                //_XDPRINTF_("  BAR-%u, Mem, range=%x-%x\n", i,
                                //           (bar_value & ~(0xF)), (bar_value & ~(0xF)) + bar_size) ;
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_MEM;
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=(bar_value & ~(0xF));
                                sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=(bar_value & ~(0xF)) + bar_size;

                            }

                            xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_BAR0+(i*4), sizeof(u32), bar_value);
                        }else{
                            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].extent_type=_MEMIOREGIONS_EXTENTS_TYPE_NONE;
                            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_start=0;
                            sysdev_memioregions[numentries_sysdev_memioregions].memioextents[i].addr_end=0;
                        }
                    }
                }


                //restore command register
                xmhf_baseplatform_arch_x86_pci_type1_write(b, d, f, PCI_CONF_HDR_IDX_COMMAND, sizeof(u16), command);
                numentries_sysdev_memioregions++;
            }
		}
	}


    //be verbose about the system devices and their MM(IO) extents
    {
        u32 i, j;
        for(i=0; i <numentries_sysdev_memioregions; i++){
            _XDPRINTF_("Device idx=%u, %x:%x:%x (vid:did=%x:%x, type=%x)...\n", i, sysdev_memioregions[i].b,
                       sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
                       sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype);
            for(j=0; j < PCI_CONF_MAX_BARS; j++){
                switch(sysdev_memioregions[i].memioextents[j].extent_type){
                    case _MEMIOREGIONS_EXTENTS_TYPE_IO:
                        _XDPRINTF_("  IO region: %x - %x\n", sysdev_memioregions[i].memioextents[j].addr_start,
                                        sysdev_memioregions[i].memioextents[j].addr_end);
                        break;

                    case _MEMIOREGIONS_EXTENTS_TYPE_MEM:
                        _XDPRINTF_("  MEM region: %x - %x\n", sysdev_memioregions[i].memioextents[j].addr_start,
                                        sysdev_memioregions[i].memioextents[j].addr_end);
                        break;

                    default:
                        break;
                }
            }
        }
    }

}



//initialize vtd hardware and return vt-d pagewalk level
static u32 _geec_prime_vtd_initialize(u32 vtd_ret_addr){
    u32 vtd_pagewalk_level = VTD_PAGEWALK_NONE;
    //vtd_drhd_handle_t vtd_drhd_maxhandle=0;
	vtd_drhd_handle_t drhd_handle;
	//u32 vtd_dmar_table_physical_address=0;
    vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
    u32 i, b, d, f;


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

/*    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        //for now detect rich guest slab and allocate all platform devices to it
        if(_xmhfhic_common_slab_info_table[i].slab_devices.desc_valid &&
            _xmhfhic_common_slab_info_table[i].slab_devices.numdevices == 0xFFFFFFFFUL)
            return i;
    }

    return 0xFFFFFFFFUL;
*/
    //XXX: allocate all devices to rich guest slab for now
    return XMHFGEEC_SLAB_XG_RICHGUEST;

}





void xmhfhic_arch_setup_slab_device_allocation(void){
    u32 i, vtd_pagewalk_level;
    //slab_platformdevices_t ddescs;
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

    //enumerate system devices
    _sda_enumerate_system_devices();

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


    //allocate system devices to slabs for direct DMA
    {
        u32 i;
        for(i=0; i <numentries_sysdev_memioregions; i++){
            if(sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_GENERAL ||
               sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_BRIDGE ||
               sysdev_memioregions[i].dtype == SYSDEV_MEMIOREGIONS_DTYPE_UNKNOWN){

                spl.dst_uapifn = XMHFGEEC_UAPI_SDEVPGTBL_BINDDEVICE;
                binddevicep->dst_slabid = _geec_prime_getslabfordevice(sysdev_memioregions[i].b, sysdev_memioregions[i].d, sysdev_memioregions[i].f);
                if(binddevicep->dst_slabid == 0xFFFFFFFFUL){
                    _XDPRINTF_("Could not find slab for device %x:%x:%x (vid:did=%x:%x, type=%x), skipping...\n", sysdev_memioregions[i].b,
                               sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
                               sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype);
                }else{
                    binddevicep->bus = sysdev_memioregions[i].b;
                    binddevicep->dev = sysdev_memioregions[i].d;
                    binddevicep->func = sysdev_memioregions[i].f;
                    binddevicep->pagewalk_level = vtd_pagewalk_level;
                    XMHF_SLAB_CALLNEW(&spl);
                    _XDPRINTF_("Allocated device %x:%x:%x (vid:did=%x:%x, type=%x) to slab %u...\n", sysdev_memioregions[i].b,
                               sysdev_memioregions[i].d, sysdev_memioregions[i].f, sysdev_memioregions[i].vendor_id,
                               sysdev_memioregions[i].device_id, sysdev_memioregions[i].dtype, binddevicep->dst_slabid);
                }
            }
        }
    }


}


















//////
// setup (unverified) slab iotbl
/////
void geec_prime_setup_slab_iotbl(void){
    u32 i;
    u32 slabtype;
    slab_params_t spl;
    xmhfgeec_uapi_slabiotbl_init_params_t *initp =
        (xmhfgeec_uapi_slabiotbl_init_params_t *)spl.in_out_params;

    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABIOTBL;
    spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid here



    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        slabtype = _xmhfhic_common_slab_info_table[i].slabtype;

        switch(slabtype){
            case XMHFGEEC_SLABTYPE_uVT_PROG:
            case XMHFGEEC_SLABTYPE_uVU_PROG:
            case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
            case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:
            case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
                spl.dst_uapifn = XMHFGEEC_UAPI_SLABIOTBL_INIT;
                initp->dst_slabid = i;
                XMHF_SLAB_CALLNEW(&spl);
            }
            break;

            default:
                break;
        }
    }


	_XDPRINTF_("%s: setup unverified slab legacy I/O permission tables\n", __func__);

}































//////////////////////////////////////////////////////////////////////////////
// setup slab memory page tables (smt)

#define _SLAB_SPATYPE_MASK_SAMESLAB             (0x100)

#define	_SLAB_SPATYPE_SLAB_CODE					(0x0)
#define	_SLAB_SPATYPE_SLAB_DATA	    			(0x1)
#define _SLAB_SPATYPE_SLAB_STACK				(0x2)
#define _SLAB_SPATYPE_SLAB_DMADATA				(0x3)
#define _SLAB_SPATYPE_SLAB_DEVICEMMIO           (0x4)
#define _SLAB_SPATYPE_GEEC_PRIME_IOTBL          (0x5)

#define _SLAB_SPATYPE_OTHER	    				(0x6)


static slab_devicemap_t _smt_slab_devicemap[XMHFGEEC_TOTAL_SLABS];


//returns true if a given device vendor_id:device_id is in the slab device exclusion
//list
static bool _geec_prime_smt_populate_slabdevicemap_isdevinexcl(u32 slabid, u32 vendor_id, u32 device_id){
    u32 i;

    for(i=0; i < _xmhfhic_common_slab_info_table[slabid].excl_devices_count; i++){
        if(_xmhfhic_common_slab_info_table[slabid].excl_devices[i].vendor_id == vendor_id &&
           _xmhfhic_common_slab_info_table[slabid].excl_devices[i].device_id == device_id)
            return true;
    }

    return false;
}

static void _geec_prime_smt_populate_slabdevicemap(void){
    u32 i, j, k;

    _XDPRINTF_("%s: numentries_sysdev_mmioregions=%u\n", __func__,
               numentries_sysdev_memioregions);

    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        _smt_slab_devicemap[i].device_count = 0;

        for(j=0; j < _xmhfhic_common_slab_info_table[i].incl_devices_count; j++){
            if( _xmhfhic_common_slab_info_table[i].incl_devices[j].vendor_id == 0xFFFF &&
               _xmhfhic_common_slab_info_table[i].incl_devices[j].device_id == 0xFFFF){
                for(k=0; k < numentries_sysdev_memioregions; k++){
                    if(!_geec_prime_smt_populate_slabdevicemap_isdevinexcl(i, sysdev_memioregions[k].vendor_id, sysdev_memioregions[k].device_id)){
                        if( _smt_slab_devicemap[i].device_count >= MAX_PLATFORM_DEVICES){
                            _XDPRINTF_("%s: Halting! device_count >= MAX_PLATFORM_DEVICES\n", __func__);
                            HALT();
                        }
                        _smt_slab_devicemap[i].sysdev_mmioregions_indices[_smt_slab_devicemap[i].device_count]=k;
                        _smt_slab_devicemap[i].device_count++;

                    }
                }
            }else{
                for(k=0; k < numentries_sysdev_memioregions; k++){
                    if( (sysdev_memioregions[k].vendor_id == _xmhfhic_common_slab_info_table[i].incl_devices[j].vendor_id) &&
                        (sysdev_memioregions[k].device_id == _xmhfhic_common_slab_info_table[i].incl_devices[j].device_id) &&
                        !_geec_prime_smt_populate_slabdevicemap_isdevinexcl(i, _xmhfhic_common_slab_info_table[i].incl_devices[j].vendor_id, _xmhfhic_common_slab_info_table[i].incl_devices[j].device_id)
                    ){
                        if( _smt_slab_devicemap[i].device_count >= MAX_PLATFORM_DEVICES){
                            _XDPRINTF_("%s: Halting! device_count >= MAX_PLATFORM_DEVICES\n", __func__);
                            HALT();
                        }
                        _smt_slab_devicemap[i].sysdev_mmioregions_indices[_smt_slab_devicemap[i].device_count]=k;
                        _smt_slab_devicemap[i].device_count++;

                    }
                }
            }
        }
    }


    //debug dump
    {
        u32 i, j;
        for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
            _XDPRINTF_("%s: slab %u...\n", __func__, i);
            for(j=0; j < _smt_slab_devicemap[i].device_count; j++){
                _XDPRINTF_("     device idx=%u\n", _smt_slab_devicemap[i].sysdev_mmioregions_indices[j]);
            }
        }
    }


}

static bool _geec_prime_smt_slab_getspatype_isdevicemmio(u32 slabid, u32 spa){
    u32 i, j;

    for(i=0; i < _smt_slab_devicemap[slabid].device_count; i++){
        u32 sysdev_memioregions_index = _smt_slab_devicemap[slabid].sysdev_mmioregions_indices[i];
        for(j=0; j < PCI_CONF_MAX_BARS; j++){
            if(sysdev_memioregions[sysdev_memioregions_index].memioextents[j].extent_type == _MEMIOREGIONS_EXTENTS_TYPE_MEM){
                if(spa >= sysdev_memioregions[sysdev_memioregions_index].memioextents[j].addr_start &&
                    spa < sysdev_memioregions[sysdev_memioregions_index].memioextents[j].addr_end)
                    return true;
            }
        }
    }

    return false;
}


static bool _geec_prime_smt_slab_getspatype_isiotbl(u32 slabid, u32 spa){
    u32 i;

    for(i=0; i < MAX_PLATFORM_CPUS; i++){
      if (spa >= (u32)&__xmhfhic_x86vmx_tss[i].tss_iobitmap &&
          spa < ((u32)&__xmhfhic_x86vmx_tss[i].tss_iobitmap + sizeof((u32)&__xmhfhic_x86vmx_tss[i].tss_iobitmap)) )
            return true;
    }

    return false;
}


static u32 _geec_prime_slab_getspatype(u32 slab_index, u32 spa){
	u32 i;




	//slab memory regions
	for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
		u32 mask = _xmhfhic_common_slab_info_table[i].slabtype;

        if( i == slab_index)
            mask |= _SLAB_SPATYPE_MASK_SAMESLAB;

        if(_geec_prime_smt_slab_getspatype_isiotbl(slab_index, spa))
            return _SLAB_SPATYPE_GEEC_PRIME_IOTBL | mask;
        if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_end)
            return _SLAB_SPATYPE_SLAB_CODE | mask;
        if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[1].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[1].addr_end)
            return _SLAB_SPATYPE_SLAB_DATA | mask;
        if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_end)
            return _SLAB_SPATYPE_SLAB_STACK | mask;
        if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_end)
            return _SLAB_SPATYPE_SLAB_DMADATA | mask;
        if(_geec_prime_smt_slab_getspatype_isdevicemmio(slab_index, spa))
            return _SLAB_SPATYPE_SLAB_DEVICEMMIO | mask;

	}

	return _SLAB_SPATYPE_OTHER;
}



// for VfT_PROG, uVT_PROG and uVU_PROG
static u64 _geec_prime_slab_getptflagsforspa_pae(u32 slabid, u32 spa, u32 spatype){
	u64 flags=0;
    u8 spa_slabtype, spa_slabregion;
    bool spa_sameslab=false;
	//_XDPRINTF_("\n%s: slab_index=%u, spa=%08x, spatype = %x\n", __func__, slab_index, spa, spatype);
    u32 slabtype = _xmhfhic_common_slab_info_table[slabid].slabtype;

    spa_slabregion = spatype & 0x0000000FUL;
    spa_slabtype =spatype & 0x000000F0UL;
    if(spatype & _SLAB_SPATYPE_MASK_SAMESLAB)
        spa_sameslab = true;


    switch(slabtype){
        case XMHFGEEC_SLABTYPE_uVT_PROG:
        case XMHFGEEC_SLABTYPE_uVU_PROG:{
            //self slab: code=rx, data,stack,dmadata,mmio=rw, perms=USER
            //other slab vft: code=rx, data,stack,dmadata,mmio=rw, perms=SUPER
            //SPATYPE_OTHER => rw perms=SUPER
            //anything else: mapped rw perms=SUPER
            if(spa_slabregion == _SLAB_SPATYPE_OTHER){
                flags = (u64)(_PAGE_PRESENT | _PAGE_RW);
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
                        case _SLAB_SPATYPE_GEEC_PRIME_IOTBL:
                            flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX);
                            break;
                        case _SLAB_SPATYPE_SLAB_DEVICEMMIO:
                            flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX | _PAGE_PCD);
                            break;
                        default:
                            flags = 0;
                            break;
                    }

                    if(spa_sameslab || spa_slabtype == XMHFGEEC_SLABTYPE_VfT_SENTINEL)
                        flags |= (_PAGE_USER);

                }else{
                    flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX);
                }

            }
        }
        break;



        case XMHFGEEC_SLABTYPE_VfT_PROG:{
            //self slab: code=rx, data,stack,dmadata,mmio=rw, perms=SUPER
            //other slab vft: code=rx, data,stack,dmadata,mmio=rw, perms=SUPER
            //SPATYPE_OTHER => rw perms=SUPER
            //anything else: mapped rw perms=SUPER
            if(spa_slabregion == _SLAB_SPATYPE_OTHER){
                flags = (u64)(_PAGE_PRESENT | _PAGE_RW);
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
                        case _SLAB_SPATYPE_GEEC_PRIME_IOTBL:
                            flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX);
                            break;
                        case _SLAB_SPATYPE_SLAB_DEVICEMMIO:
                            flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX | _PAGE_PCD);
                            break;
                        default:
                            flags = 0;
                            break;
                    }

                }else{
                    flags = (_PAGE_PRESENT | _PAGE_RW | _PAGE_NX);
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
static u64 _geec_prime_slab_getptflagsforspa_ept(u32 slabid, u32 spa, u32 spatype){
	u64 flags=0;
    u8 spa_slabtype, spa_slabregion;
    bool spa_sameslab=false;
	//_XDPRINTF_("\n%s: slab_index=%u, spa=%08x, spatype = %x\n", __func__, slab_index, spa, spatype);
    u32 slabtype = _xmhfhic_common_slab_info_table[slabid].slabtype;

    spa_slabregion = spatype & 0x0000000FUL;
    spa_slabtype =spatype & 0x000000F0UL;
    if(spatype & _SLAB_SPATYPE_MASK_SAMESLAB)
        spa_sameslab = true;


    switch(slabtype){

        case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
        case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:{
            //code=rx, data,stack,dmadata,mmio=rw;
            //other slabs = no mapping; other region = no mapping
            if(spa_sameslab && spa_slabregion != _SLAB_SPATYPE_OTHER){
                switch(spa_slabregion){
                    case _SLAB_SPATYPE_SLAB_CODE:
                        flags = 0x5;
                        break;
                    case _SLAB_SPATYPE_SLAB_DATA:
                    case _SLAB_SPATYPE_SLAB_STACK:
                    case _SLAB_SPATYPE_SLAB_DMADATA:
                    case _SLAB_SPATYPE_SLAB_DEVICEMMIO:
                        flags = 0x3;
                        break;
                    default:
                        flags = 0;
                        break;
                }
            }else{
                flags=0;
            }
        }
        break;

        case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
            //code,data,stack,dmadata,mmio=rwx;
            //other slabs = no mapping; other region = no mapping
            if(spa_sameslab)
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




//ept4k
static void _geec_prime_populate_slab_pagetables_ept4k(u32 slabid){
	u64 p_table_value;
	u64 gpa;
	u64 flags;
	u32 spatype;
    slab_params_t spl;
    xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;

    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
    spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid

	for(gpa=0; gpa < ADDR_4GB; gpa += PAGE_SIZE_4K){
		u32 memorytype = _geec_prime_vmx_getmemorytypeforphysicalpage((u64)gpa);
        spatype = _geec_prime_slab_getspatype(slabid, (u32)gpa);
        flags = _geec_prime_slab_getptflagsforspa_ept(slabid, (u32)gpa, spatype);

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
	for(gpa=ADDR_LIBXMHFDEBUGDATA_START; gpa < ADDR_LIBXMHFDEBUGDATA_END; gpa += PAGE_SIZE_4K){
        spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = slabid;
        setentryforpaddrp->gpa = gpa;
        p_table_value = (u64) (gpa)  | ((u64)6 << 3) | 0x7 ;	//present, WB, track host MTRR
        setentryforpaddrp->entry = p_table_value;
        XMHF_SLAB_CALLNEW(&spl);
	}
#endif


}

//pae4k
static void _geec_prime_populate_slab_pagetables_pae4k(u32 slabid){
	u64 gpa;
	u64 flags;
	u32 spatype;
    u32 spa_slabregion, spa_slabtype;
    u32 slabtype = _xmhfhic_common_slab_info_table[slabid].slabtype;


    slab_params_t spl;
    xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
        (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)spl.in_out_params;

    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
    spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid

	for(gpa=0; gpa < ADDR_4GB; gpa += PAGE_SIZE_4K){
        spatype =  _geec_prime_slab_getspatype(slabid, (u32)gpa);
        spa_slabregion = spatype & 0x0000000FUL;
        spa_slabtype =spatype & 0x000000F0UL;
        flags = _geec_prime_slab_getptflagsforspa_pae(slabid, (u32)gpa, spatype);
        //_XDPRINTF_("gpa=%08x, flags=%016llx\n", (u32)gpa, flags);

        if(spa_slabregion == _SLAB_SPATYPE_GEEC_PRIME_IOTBL &&
           slabtype != XMHFGEEC_SLABTYPE_VfT_PROG && slabtype != XMHFGEEC_SLABTYPE_VfT_SENTINEL){
            //map unverified slab iotbl instead (12K)
            spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
            setentryforpaddrp->dst_slabid = slabid;
            setentryforpaddrp->gpa = gpa;
            setentryforpaddrp->entry = pae_make_pte(_xmhfhic_common_slab_info_table[slabid].iotbl_base, flags);
            XMHF_SLAB_CALLNEW(&spl);
            //_XDPRINTF_("slab %u: iotbl mapping, orig gpa=%08x, revised entry=%016llx\n", slabid,
            //           (u32)gpa, setentryforpaddrp->entry);

            gpa += PAGE_SIZE_4K;
            spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
            setentryforpaddrp->dst_slabid = slabid;
            setentryforpaddrp->gpa = gpa;
            setentryforpaddrp->entry = pae_make_pte(_xmhfhic_common_slab_info_table[slabid].iotbl_base+PAGE_SIZE_4K, flags);
            XMHF_SLAB_CALLNEW(&spl);
            //_XDPRINTF_("slab %u: iotbl mapping, orig gpa=%08x, revised entry=%016llx\n", slabid,
            //           (u32)gpa, setentryforpaddrp->entry);

            gpa += PAGE_SIZE_4K;
            spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
            setentryforpaddrp->dst_slabid = slabid;
            setentryforpaddrp->gpa = gpa;
            setentryforpaddrp->entry = pae_make_pte(_xmhfhic_common_slab_info_table[slabid].iotbl_base+(2*PAGE_SIZE_4K), flags);
            XMHF_SLAB_CALLNEW(&spl);
            //_XDPRINTF_("slab %u: iotbl mapping, orig gpa=%08x, revised entry=%016llx\n", slabid,
            //           (u32)gpa, setentryforpaddrp->entry);

            gpa += PAGE_SIZE_4K;
        }else{
            spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
            setentryforpaddrp->dst_slabid = slabid;
            setentryforpaddrp->gpa = gpa;
            setentryforpaddrp->entry = pae_make_pte(gpa, flags);
            XMHF_SLAB_CALLNEW(&spl);
        }

	}

#if defined (__DEBUG_SERIAL__)
	for(gpa=ADDR_LIBXMHFDEBUGDATA_START; gpa < ADDR_LIBXMHFDEBUGDATA_END; gpa += PAGE_SIZE_4K){
        spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR;
        setentryforpaddrp->dst_slabid = slabid;
        setentryforpaddrp->gpa = gpa;
        setentryforpaddrp->entry = pae_make_pte(gpa, (_PAGE_PRESENT |  _PAGE_RW | _PAGE_USER));
        XMHF_SLAB_CALLNEW(&spl);
	}
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

    _geec_prime_smt_populate_slabdevicemap();
    _XDPRINTF_("%s: populated slab device map\n", __func__);

    //_XDPRINTF_("%s: Halting - wip!\n", __func__);
    //HALT();

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



















































//////
// (SMP) CPU state setup code
//////


//set IOPl to CPl-3
static void __xmhfhic_x86vmx_setIOPL3(u64 cpuid){
    u32 eflags;
    eflags = CASM_FUNCCALL(read_eflags,CASM_NOPARAM);
    //eflags |= EFLAGS_IOPL;
    eflags &= ~(EFLAGS_IOPL); //clear out IOPL bits
    //eflags |= 0x00000000; //set IOPL to 0

 CASM_FUNCCALL(write_eflags,eflags);
}


//////////////////////////////////////////////////////////////////////////////
// switch to smp





static void __xmhfhic_smp_cpu_x86_savecpumtrrstate(void){
	xmhfhw_cpu_x86_save_mtrrs(&_mtrrs);
}

static void __xmhfhic_smp_cpu_x86_restorecpumtrrstate(void){
	xmhfhw_cpu_x86_restore_mtrrs(&_mtrrs);
}


//wake up APs using the LAPIC by sending the INIT-SIPI-SIPI IPI sequence
static void __xmhfhic_smp_cpu_x86_wakeupAPs(void){
	u32 eax, edx;
	volatile u32 *icr;

	//read LAPIC base address from MSR
	rdmsr(MSR_APIC_BASE, &eax, &edx);
	HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G

	//construct the command register address (offset 0x300)
	icr = (u32 *) (((u32)eax & 0xFFFFF000UL) + 0x300);

	//our AP boot-strap code is at physical memory location 0x10000.
	//so use 0x10 as the vector (0x10000/0x1000 = 0x10)

	//send INIT
	*icr = 0x000c4500UL;

	xmhf_baseplatform_arch_x86_udelay(10000);

	//wait for command completion
	{
		u32 val;
		do{
		  val = *icr;
		}while( (val & 0x1000) );
	}

	//send SIPI (twice as per the MP protocol)
	{
		int i;
		for(i=0; i < 2; i++){
			*icr = 0x000c4610UL;
			xmhf_baseplatform_arch_x86_udelay(200);
			//wait for command completion
			{
			  u32 val;
			  do{
				val = *icr;
			  }while( (val & 0x1000) );
			}
		}
	}

}



//wake up application processors (cores) in the system
static void __xmhfhic_smp_container_vmx_wakeupAPs(void){
    static x86smp_apbootstrapdata_t apdata;

    apdata.ap_cr3 = CASM_FUNCCALL(read_cr3,CASM_NOPARAM);
    apdata.ap_cr4 = CASM_FUNCCALL(read_cr4,CASM_NOPARAM);
    apdata.ap_entrypoint = (u32)&__xmhfhic_ap_entry;
    apdata.ap_gdtdesc_limit = sizeof(apdata.ap_gdt) - 1;
    //apdata.ap_gdtdesc_base = (X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_gdt);
    apdata.ap_gdtdesc_base = (X86SMP_APBOOTSTRAP_DATASEG << 4) + 48;
    apdata.ap_cs_selector = __CS_CPL0;
    apdata.ap_eip = (X86SMP_APBOOTSTRAP_CODESEG << 4);
    //apdata.cpuidtable = (u32)&__xmhfhic_x86vmx_cpuidtable;
    apdata.ap_gdt[0] = 0x0000000000000000ULL;
    apdata.ap_gdt[1] = 0x00cf9a000000ffffULL;
    apdata.ap_gdt[2] = 0x00cf92000000ffffULL;

    _XDPRINTF_("%s: sizeof(apdata)=%u bytes\n", __func__, sizeof(apdata));
    _XDPRINTF_("  apdata.ap_gdtdesc_limit at %08x\n", &apdata.ap_gdtdesc_limit);
    _XDPRINTF_("  apdata.ap_gdt at %08x\n", &apdata.ap_gdt);

    memcpy((void *)(X86SMP_APBOOTSTRAP_DATASEG << 4), (void *)&apdata, sizeof(apdata));

    memcpy((void *)(X86SMP_APBOOTSTRAP_CODESEG << 4), (void *)&_ap_bootstrap_code, PAGE_SIZE_4K);

#if defined (__DRT__)
    {
        txt_heap_t *txt_heap;
        os_mle_data_t *os_mle_data;
        mle_join_t *mle_join;
        sinit_mle_data_t *sinit_mle_data;
        os_sinit_data_t *os_sinit_data;

        txt_heap = get_txt_heap();
        os_mle_data = get_os_mle_data_start(txt_heap);
        sinit_mle_data = get_sinit_mle_data_start(txt_heap);
        os_sinit_data = get_os_sinit_data_start(txt_heap);

        // enable SMIs on BSP before waking APs (which will enable them on APs)
        // because some SMM may take immediate SMI and hang if AP gets in first
        //_XDPRINTF_("Enabling SMIs on BSP\n");
        //__getsec_smctrl();

        //mle_join = (mle_join_t *)((u32)(X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_gdtdesc_limit));
        mle_join = (mle_join_t *)((u32)(X86SMP_APBOOTSTRAP_DATASEG << 4) + 16);

        _XDPRINTF_("\nBSP: mle_join.gdt_limit = %x", mle_join->gdt_limit);
        _XDPRINTF_("\nBSP: mle_join.gdt_base = %x", mle_join->gdt_base);
        _XDPRINTF_("\nBSP: mle_join.seg_sel = %x", mle_join->seg_sel);
        _XDPRINTF_("\nBSP: mle_join.entry_point = %x", mle_join->entry_point);

        write_priv_config_reg(TXTCR_MLE_JOIN, (uint64_t)(unsigned long)mle_join);

        if (os_sinit_data->capabilities & TXT_CAPS_T_RLP_WAKE_MONITOR) {
            _XDPRINTF_("\nBSP: joining RLPs to MLE with MONITOR wakeup");
            _XDPRINTF_("\nBSP: rlp_wakeup_addr = 0x%x", sinit_mle_data->rlp_wakeup_addr);
            *((uint32_t *)(unsigned long)(sinit_mle_data->rlp_wakeup_addr)) = 0x01;
        }else {
            _XDPRINTF_("\nBSP: joining RLPs to MLE with GETSEC[WAKEUP]");
            __getsec_wakeup();
            _XDPRINTF_("\nBSP: GETSEC[WAKEUP] completed");
        }
    }

#else //!__DRT__

    _XDPRINTF_("\nBSP: Using APIC to awaken APs...");
    __xmhfhic_smp_cpu_x86_wakeupAPs();
    _XDPRINTF_("\nBSP: APs should be awake.");

#endif


}

//initialize SMP
static bool __xmhfhic_smp_arch_smpinitialize(void){
	u32 i;

    //save cpu MTRR state which we will later replicate on all APs
	#if !defined(__XMHF_VERIFICATION__)
	__xmhfhic_smp_cpu_x86_savecpumtrrstate();
    #endif

    //save page table base which we will later replicate on all APs
    _ap_cr3 = CASM_FUNCCALL(read_cr3,CASM_NOPARAM);

	//wake up APS
	if(xcbootinfo->cpuinfo_numentries > 1){
	  __xmhfhic_smp_container_vmx_wakeupAPs();
	}

	//fall through to common code
	_XDPRINTF_("%s: Relinquishing BSP thread and moving to common...\n", __func__);
	__xmhfhic_smp_cpu_x86_smpinitialize_commonstart();

	_XDPRINTF_("%s:%u: Must never get here. Halting\n", __func__, __LINE__);
	HALT();

}



//common function which is entered by all CPUs upon SMP initialization
//note: this is specific to the x86 architecture backend
void __xmhfhic_smp_cpu_x86_smpinitialize_commonstart(void){
	u32 cpuid;
	#if !defined(__XMHF_VERIFICATION__)
	//cpuid  = __xmhfhic_x86vmx_cpuidtable[xmhf_baseplatform_arch_x86_getcpulapicid()];
    cpuid  = xmhf_baseplatform_arch_x86_getcpulapicid();
    #endif

    xmhfhic_smp_entry(cpuid);
}


void xmhfhic_arch_switch_to_smp(void){
/*	//initialize cpu table and total platform CPUs
	{
	    u32 i, j;
	    for(i=0; i < MAX_X86_APIC_ID; i++)
           // __xmhfhic_x86vmx_cpuidtable[i] = 0xFFFFFFFFFFFFFFFFULL;
            __xmhfhic_x86vmx_cpuidtable[i] = 0xFFFFFFFFUL;

	    for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
            u64 value = i;

            if(xcbootinfo->cpuinfo_buffer[i].isbsp)
                //value |= 0x8000000000000000ULL;
                value |= 0x80000000UL;

            //XXX: TODO sanity check xcbootinfo->cpuinfo_buffer[i].lapic_id < MAX_X86_APIC_ID
            __xmhfhic_x86vmx_cpuidtable[xcbootinfo->cpuinfo_buffer[i].lapic_id] = value;
        }
	}*/

    __xmhfhic_smp_arch_smpinitialize();

}


void xmhfhic_smp_entry(u32 cpuid){
    //bool isbsp = (cpuid & 0x80000000UL) ? true : false;
    bool isbsp = xmhfhw_lapic_isbsp();
    #if defined (__XMHF_VERIFICATION__)
    cpuid = 0;
    isbsp = true;
    #endif // defined


    //[debug] halt all APs
    //if(!isbsp){
    //    _XDPRINTF_("%s[%u,%u]: esp=%08x. AP Halting!\n",
    //        __func__, (u16)cpuid, isbsp, CASM_FUNCCALL(read_esp,));
    //    HALT();
    //}

    _XDPRINTF_("%s[%u,%u]: esp=%08x. Starting...\n",
            __func__, cpuid, isbsp, CASM_FUNCCALL(read_esp,CASM_NOPARAM));

    xmhf_hic_arch_setup_cpu_state((u16)cpuid);

    //_XDPRINTF_("%s[%u,%u]: Halting!\n", __func__, (u16)cpuid, isbsp);
    //HALT();


    //relinquish HIC initialization and move on to the first slab
    _XDPRINTF_("%s[%u]: proceeding to call init slab at %x\n", __func__, (u16)cpuid,
                _xmhfhic_common_slab_info_table[XMHFGEEC_SLAB_XC_INIT].entrystub);

    //xmhfhic_arch_relinquish_control_to_init_slab(cpuid,
    //    _xmhfhic_common_slab_info_table[XMHFGEEC_SLAB_XC_INIT].entrystub,
    //    _xmhfhic_common_slab_info_table[XMHFGEEC_SLAB_XC_INIT].archdata.mempgtbl_cr3,
    //    _xmhfhic_common_slab_info_table[XMHFGEEC_SLAB_XC_INIT].archdata.slabtos[(u32)cpuid]);

    {
        slab_params_t sp;

        memset(&sp, 0, sizeof(sp));
        sp.cpuid = cpuid;
        sp.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
        sp.dst_slabid = XMHFGEEC_SLAB_XC_INIT;
        XMHF_SLAB_CALLNEW(&sp);
    }


    _XDPRINTF_("%s[%u,%u]: Should never be here. Halting!\n", __func__, (u16)cpuid, isbsp);
    HALT();

}



//////////////////////////////////////////////////////////////////////////////





/////////////////////////////////////////////////////////////////////
// setup base CPU data structures

//initialize GDT
static void __xmhfhic_x86vmx_initializeGDT(void){
		u32 i;

		for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
            TSSENTRY *t;
            u32 tss_idx = xcbootinfo->cpuinfo_buffer[i].lapic_id;
            u32 tss_base=(u32)&__xmhfhic_x86vmx_tss[tss_idx].tss_mainblock;

            //TSS descriptor
            t= (TSSENTRY *)&__xmhfhic_x86vmx_gdt_start[(__TRSEL/8)+(i*2)];
            t->attributes1= 0xE9;
            t->limit16_19attributes2= 0x0;
            t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
            t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
            t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);
            //t->limit0_15=0x67;
            //t->limit0_15=sizeof(tss_t)-1;
            t->limit0_15=(4*PAGE_SIZE_4K)-1;

            _XDPRINTF_("%s: setup TSS CPU idx=%u with base address=%x, iobitmap=%x\n, size=%u bytes", __func__,
                       tss_idx, tss_base, (u32)&__xmhfhic_x86vmx_tss[tss_idx].tss_iobitmap, t->limit0_15);

		}

}

//initialize IDT
static void __xmhfhic_x86vmx_initializeIDT(void){
	u32 i;

	for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
		__xmhfhic_x86vmx_idt_start[i].isrLow= (u16)__xmhfhic_exceptionstubs[i];
		__xmhfhic_x86vmx_idt_start[i].isrHigh= (u16) ( (u32)__xmhfhic_exceptionstubs[i] >> 16 );
		__xmhfhic_x86vmx_idt_start[i].isrSelector = __CS_CPL0;
		__xmhfhic_x86vmx_idt_start[i].count=0x0;
		__xmhfhic_x86vmx_idt_start[i].type=0xEE;	//32-bit interrupt gate
                                //present=1, DPL=11b, system=0, type=1110b
        //__xmhfhic_x86vmx_idt_start[i].offset3263=0;
        //__xmhfhic_x86vmx_idt_start[i].reserved=0;
	}

}


//initialize TSS
static void __xmhfhic_x86vmx_initializeTSS(void){
		u32 i;

		//initialize TSS descriptors for all CPUs
		for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
            u32 tss_idx = xcbootinfo->cpuinfo_buffer[i].lapic_id;

            memset(&__xmhfhic_x86vmx_tss[tss_idx], 0, sizeof(__xmhfhic_x86vmx_tss[tss_idx]));
            tss_t *tss= (tss_t *)__xmhfhic_x86vmx_tss[tss_idx].tss_mainblock;
            tss->esp0 = (u32) ( &__xmhfhic_x86vmx_tss_stack[tss_idx] + sizeof(__xmhfhic_x86vmx_tss_stack[0]) );
            tss->ss0 = __DS_CPL0;
            tss->iotbl_addr = (u32)&__xmhfhic_x86vmx_tss[tss_idx].tss_iobitmap - (u32)&__xmhfhic_x86vmx_tss[tss_idx].tss_mainblock;
            _XDPRINTF_("%s: tss_idx=%u, iotbl_addr=%x\n", __func__, tss_idx,
                       tss->iotbl_addr);
		}
}


void xmhfhic_arch_setup_base_cpu_data_structures(void){

    //initialize GDT
    #if !defined(__XMHF_VERIFICATION__)
    __xmhfhic_x86vmx_initializeGDT();
    #endif

    //initialize IDT
    __xmhfhic_x86vmx_initializeIDT();

    //initialize TSS
    __xmhfhic_x86vmx_initializeTSS();

}









//////////////////////////////////////////////////////////////////////////////
// setup cpu state for hic












static bool __xmhfhic_x86vmx_setupvmxstate(u64 cpuid){
    u32 cpuindex = (u32)cpuid;
	const u32 vmx_msr_area_msrs[] = {MSR_EFER, MSR_IA32_PAT}; //critical MSRs that need to be saved/restored across guest VM switches
	const unsigned int vmx_msr_area_msrs_count = (sizeof(vmx_msr_area_msrs)/sizeof(vmx_msr_area_msrs[0]));	//count of critical MSRs that need to be saved/restored across VM switches
	u32 lodword, hidword;
	u64 vmcs_phys_addr = hva2spa(__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmcs_region);


	//save contents of VMX MSRs as well as MSR EFER and EFCR
	{
		u32 i;
		u32 eax, edx;
		for(i=0; i < IA32_VMX_MSRCOUNT; i++){
			rdmsr( (IA32_VMX_BASIC_MSR + i), &eax, &edx);
			__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[i] = (u64)edx << 32 | (u64) eax;
		}

		rdmsr(MSR_EFER, &eax, &edx);
		__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_efer = (u64)edx << 32 | (u64) eax;
		rdmsr(MSR_EFCR, &eax, &edx);
		__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_efcr = (u64)edx << 32 | (u64) eax;
  	}

 CASM_FUNCCALL(write_cr4, CASM_FUNCCALL(read_cr4,CASM_NOPARAM) |  CR4_VMXE);

#if !defined (__XMHF_VERIFICATION__)
	//enter VMX root operation using VMXON
	{
		u32 retval=0;
		u64 vmxonregion_paddr = hva2spa((void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmxon_region);
		//set VMCS rev id
		*((u32 *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmxon_region) = (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

        if(!__vmx_vmxon(vmxonregion_paddr)){
			_XDPRINTF_("%s(%u): unable to enter VMX root operation\n", __func__, (u32)cpuid);
			return false;
        }
	}

	//clear VMCS
	if(!__vmx_vmclear((u64)vmcs_phys_addr))
		return false;

	//set VMCS revision id
	*((u32 *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmcs_region) = (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

	//load VMPTR
	if(!__vmx_vmptrld((u64)vmcs_phys_addr))
		return false;
#endif //__XMHF_VERIFICATION__


	//setup host state
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CR0, CASM_FUNCCALL(read_cr0,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CR4, CASM_FUNCCALL(read_cr4,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CR3, CASM_FUNCCALL(read_cr3,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CS_SELECTOR, CASM_FUNCCALL(read_segreg_cs,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_DS_SELECTOR, CASM_FUNCCALL(read_segreg_ds,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_ES_SELECTOR, CASM_FUNCCALL(read_segreg_es,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_FS_SELECTOR, CASM_FUNCCALL(read_segreg_fs,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_GS_SELECTOR, CASM_FUNCCALL(read_segreg_gs,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SS_SELECTOR, CASM_FUNCCALL(read_segreg_ss,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_TR_SELECTOR, CASM_FUNCCALL(read_tr_sel,CASM_NOPARAM));
	//_XDPRINTF_("%s: read_tr_sel = %08x\n", __func__, CASM_FUNCCALL(read_tr_sel,CASM_NOPARAM));
	//_XDPRINTF_("%s: HOST TR SELECTOR = %08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_HOST_TR_SELECTOR));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_GDTR_BASE, CASM_FUNCCALL(xmhf_baseplatform_arch_x86_getgdtbase,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_IDTR_BASE, CASM_FUNCCALL(xmhf_baseplatform_arch_x86_getidtbase,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_TR_BASE, CASM_FUNCCALL(xmhf_baseplatform_arch_x86_gettssbase,CASM_NOPARAM));

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_RIP, _geec_sentinel_intercept_casmstub);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_RSP, CASM_FUNCCALL(read_rsp,CASM_NOPARAM));
	rdmsr(IA32_SYSENTER_CS_MSR, &lodword, &hidword);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SYSENTER_CS, lodword);
	rdmsr(IA32_SYSENTER_ESP_MSR, &lodword, &hidword);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SYSENTER_ESP, (((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_SYSENTER_EIP_MSR, &lodword, &hidword);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SYSENTER_EIP, (((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_MSR_FS_BASE, &lodword, &hidword);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_FS_BASE, (((u64)hidword << 32) | (u64)lodword) );
	rdmsr(IA32_MSR_GS_BASE, &lodword, &hidword);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_GS_BASE, (((u64)hidword << 32) | (u64)lodword) );

	//setup default VMX controls
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_PIN_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_CONTROLS, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_CONTROLS, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);

    /*
    x86_64
    //64-bit host
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_CONTROLS, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_EXIT_CONTROLS) | (1 << 9)) );
    */

	//IO bitmap support
 //CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL, (u32)&__xmhfhic_x86vmx_tss[cpuindex].tss_iobitmap);
 //CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH, 0);
 //CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL, (u32)&__xmhfhic_x86vmx_tss[cpuindex].tss_iobitmap + PAGE_SIZE_4K);
 //CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 25)) );

	//MSR bitmap support
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_MSR_BITMAPS_ADDRESS_FULL, hva2spa(__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrbitmaps_region ));
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 28)) );


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_PAGEFAULT_ERRORCODE_MASK, 0x00000000);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_PAGEFAULT_ERRORCODE_MATCH, 0x00000000);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EXCEPTION_BITMAP, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR3_TARGET_COUNT, 0);

	//activate secondary processor controls
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (u32) (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 31)) );

	//setup unrestricted guest
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 << 7)) );

	//setup VMCS link pointer
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_VMCS_LINK_POINTER_FULL, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_VMCS_LINK_POINTER_HIGH, 0xFFFFFFFFUL);

	//setup NMI intercept for core-quiescing
	//XXX: needs to go in xcinit/richguest slab
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_PIN_BASED) | (u64)(1 << 3) ) );

	//trap access to CR0 fixed 1-bits
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR0_MASK, (u32)(((((u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR] & ~(CR0_PE)) & ~(CR0_PG)) | CR0_CD) | CR0_NW) );

	//trap access to CR4 fixed bits (this includes the VMXE bit)
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR4_MASK, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR4_SHADOW, (u64)CR4_VMXE);

	//setup memory protection
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 <<1) | (u64)(1 << 5)) );
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VPID, 0); //[need to populate in sentinel]
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_FULL, 0); // [need to populate in sentinel]
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_HIGH, 0); // [need to populate in sentinel]
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) & (u64)~(1 << 15) & (u64)~(1 << 16)) );

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR0, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR0_SHADOW, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR0));

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR4, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_EXCEPTION_ERRORCODE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_INTERRUPTION_INFORMATION, 0);


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RSP, 0); //[need to populate in sentinel]

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RIP, 0); // [need to populate in sentinel]
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ACTIVITY_STATE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RFLAGS, (1 <<1) | (EFLAGS_IOPL));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_INTERRUPTIBILITY, 0);


    //IDTR
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_IDTR_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_IDTR_LIMIT, 0);



    //LDTR, unusable
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_LDTR_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_LDTR_LIMIT, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_LDTR_SELECTOR, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_LDTR_ACCESS_RIGHTS, 0x10000);



/*
    //64-bit specific guest slab setup
    {

        //Critical MSR load/store
        {
            u32 i;
            msr_entry_t *hmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region;
            msr_entry_t *gmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region;

            //store host and guest initial values of the critical MSRs
            for(i=0; i < vmx_msr_area_msrs_count; i++){
                u32 msr, eax, edx;
                msr = vmx_msr_area_msrs[i];
                rdmsr(msr, &eax, &edx);

                //host MSR values will be what we get from RDMSR
                hmsr[i].index = msr;
                hmsr[i].data = ((u64)edx << 32) | (u64)eax;

                //adjust and populate guest MSR values according to the MSR
                gmsr[i].index = msr;
                gmsr[i].data = ((u64)edx << 32) | (u64)eax;
                switch(msr){
                    case MSR_EFER:{
                        //gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_LME);
                        //gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_LMA);
                        //gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_SCE);
                        //gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_NXE);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_IA32_EFER_FULL, gmsr[i].data);

                    }
                    break;

                    default:
                        break;
                }

            }

            //host MSR load on exit, we store it ourselves before entry
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, hva2spa((void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

            //guest MSR load on entry, store on exit
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, hva2spa((void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, hva2spa((void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);

        }


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR4, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4) | CR4_PAE | CR4_PSE) );

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 9)) );
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 15)) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE0_FULL, _guestslab1_init_pdpt[0] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE1_FULL, _guestslab1_init_pdpt[1] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE2_FULL, _guestslab1_init_pdpt[2] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE3_FULL, _guestslab1_init_pdpt[3] );


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, &_guestslab1_init_pml4t );


        //TR, should be usable for VMX to work, but not used by guest
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_LIMIT, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_SELECTOR, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_ACCESS_RIGHTS, 0x8B);

        //CS, DS, ES, FS, GS and SS segments
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_SELECTOR, 0x8);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_ACCESS_RIGHTS, 0xa09b);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_ACCESS_RIGHTS, 0xa093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_ACCESS_RIGHTS, 0xa093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_ACCESS_RIGHTS, 0xa093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_ACCESS_RIGHTS, 0xa093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_ACCESS_RIGHTS, 0xa093);


        //GDTR
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_BASE, &_guestslab1_init_gdt_start);
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_LIMIT, (sizeof(_guestslab1_init_gdt_start)-1) );


    }
*/

    //32-bit specific guest slab setup
    {

        //Critical MSR load/store
        {
            u32 i;
            msr_entry_t *hmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region;
            msr_entry_t *gmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region;

            //store host and guest initial values of the critical MSRs
            for(i=0; i < vmx_msr_area_msrs_count; i++){
                u32 msr, eax, edx;
                msr = vmx_msr_area_msrs[i];
                rdmsr(msr, &eax, &edx);

                //host MSR values will be what we get from RDMSR
                hmsr[i].index = msr;
                hmsr[i].data = ((u64)edx << 32) | (u64)eax;

                //adjust and populate guest MSR values according to the MSR
                gmsr[i].index = msr;
                gmsr[i].data = ((u64)edx << 32) | (u64)eax;
                switch(msr){
                    case MSR_EFER:{
                        gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_LME);
                        gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_LMA);
                        gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_SCE);
                        gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_NXE);
                    }
                    break;

                    default:
                        break;
                }

            }

            //host MSR load on exit, we store it ourselves before entry
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_HIGH, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

            //guest MSR load on entry, store on exit
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_HIGH, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_HIGH, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);

        }


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4) | CR4_PAE | CR4_PSE) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 9)) );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 15)) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE0_FULL, _guestslab1_init_pdpt[0] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE1_FULL, _guestslab1_init_pdpt[1] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE2_FULL, _guestslab1_init_pdpt[2] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE3_FULL, _guestslab1_init_pdpt[3] );


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, &_guestslab1_init_pml4t );
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR3, 0 );


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR0, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0) & ~(CR0_PG) ) );
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR0_SHADOW, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR0));

        //TR, should be usable for VMX to work, but not used by guest
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_LIMIT, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_SELECTOR, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_ACCESS_RIGHTS, 0x8B);

        //CS, DS, ES, FS, GS and SS segments
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_SELECTOR, 0x8);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_ACCESS_RIGHTS, 0xc09b);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_ACCESS_RIGHTS, 0xc093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_ACCESS_RIGHTS, 0xc093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_ACCESS_RIGHTS, 0xc093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_ACCESS_RIGHTS, 0xc093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_ACCESS_RIGHTS, 0xc093);



    }



















	/*_XDPRINTF_("%s: vmcs pinbased=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_PIN_BASED));
	_XDPRINTF_("%s: pinbase MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
	_XDPRINTF_("%s: cpu_based vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_CPU_BASED));
	_XDPRINTF_("%s: cpu_based MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
	_XDPRINTF_("%s: seccpu_based vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_SECCPU_BASED));
	_XDPRINTF_("%s: seccpu_based MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	_XDPRINTF_("%s: entrycontrols vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_ENTRY_CONTROLS));
	_XDPRINTF_("%s: entrycontrols MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);
	_XDPRINTF_("%s: exitcontrols vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_EXIT_CONTROLS));
	_XDPRINTF_("%s: exitcontrols MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
	_XDPRINTF_("%s: iobitmapa vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL));
	_XDPRINTF_("%s: iobitmapb vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap load vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap store vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap exit load vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL));
	_XDPRINTF_("%s: ept pointer vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_EPT_POINTER_FULL));
    */
	_XDPRINTF_("%s: CR0 vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR0));
	_XDPRINTF_("%s: CR4 vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR4));
	_XDPRINTF_("%s: CR0 mask vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR0_MASK));
	_XDPRINTF_("%s: CR4 mask vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR4_MASK));
	_XDPRINTF_("%s: CR0 shadow vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR0_SHADOW));
	_XDPRINTF_("%s: CR4 shadow vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR4_SHADOW));


    return true;
}



void xmhf_hic_arch_setup_cpu_state(u64 cpuid){

	//replicate common MTRR state on this CPU
	#if !defined (__XMHF_VERIFICATION__)
	__xmhfhic_smp_cpu_x86_restorecpumtrrstate();
    #endif

    //load GDT
    //__xmhfhic_x86vmx_loadGDT(&__xmhfhic_x86vmx_gdt);

 CASM_FUNCCALL(xmhfhw_cpu_loadGDT,&__xmhfhic_x86vmx_gdt);
    _XDPRINTF_("%s[%u]: GDT loaded\n", __func__, (u32)cpuid);

 CASM_FUNCCALL(__xmhfhic_x86vmx_reloadCS,__CS_CPL0);
    _XDPRINTF_("%s[%u]: Reloaded CS\n", __func__, (u32)cpuid);

 CASM_FUNCCALL(__xmhfhic_x86vmx_reloadsegregs,__DS_CPL0);
    _XDPRINTF_("%s[%u]: Reloaded segment registers\n", __func__, (u32)cpuid);


    //load TR
 CASM_FUNCCALL(xmhfhw_cpu_loadTR, (__TRSEL + ((u32)cpuid * 16) ) );
    _XDPRINTF_("%s[%u]: TR loaded\n", __func__, (u32)cpuid);

    //load IDT
 CASM_FUNCCALL(xmhfhw_cpu_loadIDT,&__xmhfhic_x86vmx_idt);
    _XDPRINTF_("%s[%u]: IDT loaded\n", __func__, (u32)cpuid);

    ////turn on CR0.WP bit for supervisor mode write protection
    //write_cr0(read_cr0() | CR0_WP);
    //_XDPRINTF_("%s[%u]: Enabled supervisor mode write protection\n", __func__, (u32)cpuid);

    //set IOPL3
    __xmhfhic_x86vmx_setIOPL3(cpuid);
    _XDPRINTF_("%s[%u]: set IOPL to CPL-3\n", __func__, (u32)cpuid);


    //set LAPIC base address to preferred address
    {
        u64 msrapic = CASM_FUNCCALL(rdmsr64,MSR_APIC_BASE);
 CASM_FUNCCALL(wrmsr64,MSR_APIC_BASE, ((msrapic & 0x0000000000000FFFULL) | X86SMP_LAPIC_MEMORYADDRESS));
    }
    _XDPRINTF_("%s[%u]: set LAPIC base address to %016llx\n", __func__, (u32)cpuid, CASM_FUNCCALL(rdmsr64,MSR_APIC_BASE));

	//turn on NX protections
 CASM_FUNCCALL(wrmsr64,MSR_EFER, (rdmsr64(MSR_EFER) | (1 << EFER_NXE)) );
    _XDPRINTF_("%s[%u]: NX protections enabled\n", __func__, (u32)cpuid);


#if 0
	//enable PCIDE support
	{
 CASM_FUNCCALL(write_cr4,read_cr4() | CR4_PCIDE);
	}
    _XDPRINTF_("%s[%u]: PCIDE enabled\n", __func__, (u32)cpuid);
#endif

	//set OSXSAVE bit in CR4 to enable us to pass-thru XSETBV intercepts
	//when the CPU supports XSAVE feature
	if(xmhf_baseplatform_arch_x86_cpuhasxsavefeature()){
 CASM_FUNCCALL(write_cr4,read_cr4(CASM_NOPARAM) | CR4_OSXSAVE);
        _XDPRINTF_("%s[%u]: XSETBV passthrough enabled\n", __func__, (u32)cpuid);
	}


	//set bit 5 (EM) of CR0 to be VMX compatible in case of Intel cores
 CASM_FUNCCALL(write_cr0,read_cr0(CASM_NOPARAM) | 0x20);
    _XDPRINTF_("%s[%u]: Set CR0.EM to be VMX compatible\n", __func__, (u32)cpuid);


    //setup SYSENTER/SYSEXIT mechanism
    {
        wrmsr(IA32_SYSENTER_CS_MSR, __CS_CPL0, 0);
        wrmsr(IA32_SYSENTER_EIP_MSR, (u32)&_geec_sentinel_sysenter_casmstub, 0);
        wrmsr(IA32_SYSENTER_ESP_MSR, ((u32)_geec_primesmp_sysenter_stack[(u32)cpuid] + MAX_PLATFORM_CPUSTACK_SIZE), 0);
    }
    _XDPRINTF_("%s: setup SYSENTER/SYSEXIT mechanism\n", __func__);
    _XDPRINTF_("SYSENTER CS=%016llx\n", CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_CS_MSR));
    _XDPRINTF_("SYSENTER RIP=%016llx\n", CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_EIP_MSR));
    _XDPRINTF_("SYSENTER RSP=%016llx\n", CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_ESP_MSR));


    //setup VMX state
    if(!__xmhfhic_x86vmx_setupvmxstate(cpuid)){
        _XDPRINTF_("%s[%u]: Unable to set VMX state. Halting!\n", __func__, (u32)cpuid);
        HALT();
    }
    _XDPRINTF_("%s[%u]: Setup VMX state\n", __func__, (u32)cpuid);

}



























/////
void _geec_prime_setup_cpustate(void){

    //setup base CPU data structures
    xmhfhic_arch_setup_base_cpu_data_structures();

    //setup SMP and move on to xmhfhic_smp_entry
    xmhfhic_arch_switch_to_smp();

    //we should never get here
    _XDPRINTF_("Should never be here. Halting!\n");
    HALT();

}
































#if 0

    //debug
    _XDPRINTF_("Halting!\n");
    _XDPRINTF_("XMHF Tester Finished!\n");
    HALT();

#endif // 0
