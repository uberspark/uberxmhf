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
#include <xmhf-hic.h>
#include <xmhf-debug.h>


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











void slab_main(slab_params_t *sp){
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


    //transfer control to geec_primesmp
    {
        slab_params_t spl;
        spl.src_slabid = XMHF_HYP_SLAB_GEECPRIME;
        spl.dst_slabid = XMHF_HYP_SLAB_GEEC_PRIMESMP;
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

        for(i=0; i < XMHF_HIC_MAX_SLABS; i++){

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
            _xmhfhic_common_slab_info_table[i].archdata.slabtype =
                _xmhfhic_init_setupdata_slab_caps[i].slab_archparams;

            _xmhfhic_common_slab_info_table[i].archdata.mempgtbl_initialized=false;
            _xmhfhic_common_slab_info_table[i].archdata.devpgtbl_initialized=false;
*/
/*            #if !defined(__XMHF_VERIFICATION__)
            {
                u32 j;
                //u64 *slab_stackhdr = (u64 *)_xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_start;
                u32 *slab_stackhdr = (u32 *)_xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_start;

                if(slab_stackhdr){
                    for(j=0; j < MAX_PLATFORM_CPUS; j++)
                        _xmhfhic_common_slab_info_table[i].archdata.slabtos[j]=slab_stackhdr[j];
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

			for(i=0; i < XMHF_HIC_MAX_SLABS; i++){
				_XDPRINTF_("slab %u: dumping slab header\n", i);
				_XDPRINTF_("	slabtype=%08x\n", _xmhfhic_common_slab_info_table[i].archdata.slabtype);
				_XDPRINTF_("	slab_inuse=%s\n", ( _xmhfhic_common_slab_info_table[i].slab_inuse ? "true" : "false") );
				_XDPRINTF_("	slab_privilegemask=%08x\n", _xmhfhic_common_slab_info_table[i].slab_privilegemask);
				_XDPRINTF_("	slab_callcaps=%08x\n", _xmhfhic_common_slab_info_table[i].slab_callcaps);
				_XDPRINTF_("	slab_devices=%s\n", ( _xmhfhic_common_slab_info_table[i].slab_devices.desc_valid ? "true" : "false") );
				_XDPRINTF_("  slab_code(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_end);
				_XDPRINTF_("  slab_rwdata(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[1].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[1].addr_end);
				_XDPRINTF_("  slab_rodata(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_end);
				_XDPRINTF_("  slab_stack(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_end);
				_XDPRINTF_("  slab_dmadata(%08x-%08x)\n", _xmhfhic_common_slab_info_table[i].slab_physmem_extents[4].addr_start, _xmhfhic_common_slab_info_table[i].slab_physmem_extents[4].addr_end);
				_XDPRINTF_("  slab_entrystub=%08x\n", _xmhfhic_common_slab_info_table[i].entrystub);

                {
                    u32 j;

                    for(j=0; j < MAX_PLATFORM_CPUS; j++)
                        //_XDPRINTF_("     CPU %u: stack TOS=%016llx\n", j,
                        //       _xmhfhic_common_slab_info_table[i].archdata.slabtos[j]);
                        _XDPRINTF_("     CPU %u: stack TOS=%08x\n", j,
                               _xmhfhic_common_slab_info_table[i].archdata.slabtos[j]);
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


__attribute__((aligned(4096))) static vtd_ret_entry_t _vtd_ret[VTD_RET_MAXPTRS];
__attribute__((aligned(4096))) static vtd_cet_entry_t _vtd_cet[VTD_RET_MAXPTRS][VTD_CET_MAXPTRS];

static vtd_drhd_handle_t vtd_drhd_maxhandle=0;
static u32 vtd_pagewalk_level = VTD_PAGEWALK_NONE;
static bool vtd_initialized = false;

static u64 _platform_x86pc_vtd_setup_retcet(void){
    u32 i, j;

    for(i=0; i< VTD_RET_MAXPTRS; i++){
        _vtd_ret[i].qwords[0] = vtd_make_rete((u64)&_vtd_cet[i], VTD_RET_PRESENT);
        _vtd_ret[i].qwords[1] = 0ULL;

        for(j=0; j < VTD_CET_MAXPTRS; j++){
            _vtd_cet[i][j].qwords[0] = _vtd_cet[i][j].qwords[1] = 0ULL;
        }
    }

    return (u64)&_vtd_ret;
}

//initialize vtd hardware and setup vtd_drhd_maxhandle and _vtd_pagewalk_level
//to appropriate values. if everything went well set vtd_initialized to true
static bool _platform_x86pc_vtd_initialize(void){
    u64 vtd_ret_addr;
	vtd_drhd_handle_t drhd_handle;
	u32 vtd_dmar_table_physical_address=0;
    vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
    u32 i, b, d, f;

    //if we already setup vtd then simply return true
    if(vtd_initialized)
        return true;

	//setup basic RET/CET structure; will initially prevent DMA reads and writes
	//for the entire system
    vtd_ret_addr = _platform_x86pc_vtd_setup_retcet();

	//scan for available DRHD units in the platform
	if(!xmhfhw_platform_x86pc_vtd_scanfor_drhd_units(&vtd_drhd_maxhandle, &vtd_dmar_table_physical_address)){
        _XDPRINTF_("%s: unable to scan for DRHD units. bailing out!\n", __func__);
		return false;
	}

    _XDPRINTF_("%s: maxhandle = %u, dmar table addr=0x%08x\n", __func__,
                (u32)vtd_drhd_maxhandle, (u32)vtd_dmar_table_physical_address);



	//initialize all DRHD units
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
   		VTD_CAP_REG cap;

		_XDPRINTF_("%s: Setting up DRHD unit %u...\n", __func__, drhd_handle);

		if(!xmhfhw_platform_x86pc_vtd_drhd_initialize(drhd_handle) ){
            _XDPRINTF_("%s: error setting up DRHD unit %u. bailing out!\n", __func__, drhd_handle);
			return false;
		}

        //read and store DRHD supported page-walk length
        unpack_VTD_CAP_REG(&cap, xmhfhw_platform_x86pc_vtd_drhd_reg_read(drhd_handle, VTD_CAP_REG_OFF));
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
		if(!xmhfhw_platform_x86pc_vtd_drhd_set_root_entry_table(drhd_handle, vtd_ret_addr))
			return false;

		//invalidate caches
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(drhd_handle))
			return false;

		//enable VT-d translation
		xmhfhw_platform_x86pc_vtd_drhd_enable_translation(drhd_handle);

		//disable PMRs now (since DMA protection is active via translation)
		xmhfhw_platform_x86pc_vtd_drhd_disable_pmr(drhd_handle);

		_XDPRINTF_("%s: Successfully setup DRHD unit %u\n", __func__, drhd_handle);
	}

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	xmhfhw_sysmemaccess_writeu32(vtd_dmar_table_physical_address, 0UL);


    _XDPRINTF_("%s: final page-walk level=%u\n", __func__, vtd_pagewalk_level);

    vtd_initialized = true;

    return true;
}

#if !defined (__XMHF_VERIFICATION__)
static vtd_slpgtbl_handle_t _platform_x86pc_vtd_setup_slpgtbl(u32 slabid){
    vtd_slpgtbl_handle_t retval = {0, 0};
    u32 i, j, k, paddr=0;
    u64 default_flags = (VTD_PAGE_READ | VTD_PAGE_WRITE);

    //sanity check partition index
    if(slabid > XMHF_HIC_MAX_SLABS){
        _XDPRINTF_("%s: Error: slabid (%u) > XMHF_HIC_MAX_SLABS(%u). bailing out!\n", __func__, slabid, XMHF_HIC_MAX_SLABS);
        return retval;
    }



    //setup device memory access for the partition
    _dbuf_devpgtbl[slabid].pml4t[0] = vtd_make_pml4te((u64)_dbuf_devpgtbl[slabid].pdpt, default_flags);

    for(i=0; i < VTD_PTRS_PER_PDPT; i++){
        _dbuf_devpgtbl[slabid].pdpt[i] = vtd_make_pdpte((u64)_dbuf_devpgtbl[slabid].pdt[i], default_flags);

        for(j=0; j < VTD_PTRS_PER_PDT; j++){
            _dbuf_devpgtbl[slabid].pdt[i][j] = vtd_make_pdte((u64)_dbuf_devpgtbl[slabid].pt[i][j], default_flags);

            for(k=0; k < PAE_PTRS_PER_PT; k++){
                _dbuf_devpgtbl[slabid].pt[i][j][k] = vtd_make_pte(paddr, default_flags);
                paddr += PAGE_SIZE_4K;
            }
        }
    }

    //populate device page tables pml4t, pdpt, pdt and pt pointers in slab info table
    //XXX: these will move into devicepgtbl uapi slab
    //_xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_pml4t = &_dbuf_devpgtbl[slabid].pml4t;
    //_xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_pdpt = &_dbuf_devpgtbl[slabid].pdpt;
    //_xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_pdt = &_dbuf_devpgtbl[slabid].pdt;
    //_xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_pt = &_dbuf_devpgtbl[slabid].pt;


    retval.addr_vtd_pml4t = &_dbuf_devpgtbl[slabid].pml4t;
    retval.addr_vtd_pdpt = &_dbuf_devpgtbl[slabid].pdpt;

    return retval;
}
#endif

//static xc_platformdevice_desc_t __xmhfhic_arch_initializeandenumeratedevices(context_desc_t context_desc){
static slab_platformdevices_t __xmhfhic_arch_initializeandenumeratedevices(void){
    slab_platformdevices_t result;
    u32 b, d, f;

    result.desc_valid = false;
    result.numdevices = 0;

    //initialize vtd hardware (if it has not been initialized already)
    if(!_platform_x86pc_vtd_initialize())
        return result;

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

                result.arch_desc[result.numdevices].pci_bus=b;
                result.arch_desc[result.numdevices].pci_device=d;
                result.arch_desc[result.numdevices].pci_function=f;
                result.arch_desc[result.numdevices].vendor_id=vendor_id;
                result.arch_desc[result.numdevices].device_id=device_id;

                result.numdevices++;
			}
		}
	}

    result.desc_valid = true;
    return result;
}


static bool __xmhfhic_arch_sda_allocdevices_to_slab(u64 slabid, slab_platformdevices_t device_descs){
	vtd_drhd_handle_t drhd_handle;
    vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
    u32 i;

    if(!vtd_initialized)
        return false;

    if(!device_descs.desc_valid)
        return true;

    #if !defined (__XMHF_VERIFICATION__)
    //initialize slab device page tables (if it has not been initialized already)
    if( !_xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_initialized ){
        vtd_slpgtbl_handle = _platform_x86pc_vtd_setup_slpgtbl(slabid);

        if(vtd_slpgtbl_handle.addr_vtd_pml4t == 0 &&
            vtd_slpgtbl_handle.addr_vtd_pdpt == 0){
            _XDPRINTF_("%s: unable to initialize vt-d pagetables for slab %u\n", __func__, slabid);
            return false;
        }

        _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_initialized=true;
    }
    #endif


    for(i=0; i < device_descs.numdevices; i++){
        u32 b=device_descs.arch_desc[i].pci_bus;
        u32 d=device_descs.arch_desc[i].pci_device;
        u32 f=device_descs.arch_desc[i].pci_function;

        //sanity check b, d, f triad
        if ( !(b < PCI_BUS_MAX &&
               d < PCI_DEVICE_MAX &&
               f < PCI_FUNCTION_MAX) )
            return false;

        //b is our index into ret
        // (d* PCI_FUNCTION_MAX) + f = index into the cet
        if(vtd_pagewalk_level == VTD_PAGEWALK_4LEVEL){
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].qwords[0] =
                vtd_make_cete((u64)&_dbuf_devpgtbl[slabid].pml4t, VTD_CET_PRESENT);
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].qwords[1] =
                vtd_make_cetehigh(2, (slabid+1));
        }else if (vtd_pagewalk_level == VTD_PAGEWALK_3LEVEL){
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].qwords[0] =
                vtd_make_cete((u64)&_dbuf_devpgtbl[slabid].pdpt, VTD_CET_PRESENT);
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].qwords[1] =
                vtd_make_cetehigh(1, (slabid+1));
        }else{ //unknown page walk length, fail
            return false;
        }

    }


	//invalidate vtd caches
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(drhd_handle))
			return false;
	}

    return true;
}


static bool __xmhfhic_arch_sda_deallocdevices_from_slab(u64 slabid, slab_platformdevices_t device_descs){
	vtd_drhd_handle_t drhd_handle;
    vtd_slpgtbl_handle_t vtd_slpgtbl_handle;
    u32 i;

    if(!vtd_initialized)
        return false;

    for(i=0; i < device_descs.numdevices; i++){
        u32 b=device_descs.arch_desc[i].pci_bus;
        u32 d=device_descs.arch_desc[i].pci_device;
        u32 f=device_descs.arch_desc[i].pci_function;

        //sanity check b, d, f triad
        if ( !(b < PCI_BUS_MAX &&
               d < PCI_DEVICE_MAX &&
               f < PCI_FUNCTION_MAX) )
            return false;

        //b is our index into ret
        // (d* PCI_FUNCTION_MAX) + f = index into the cet
        _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].qwords[0] = 0;
        _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].qwords[1] = 0;
    }

	//invalidate vtd caches
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
		if(!xmhfhw_platform_x86pc_vtd_drhd_invalidatecaches(drhd_handle))
			return false;
	}

    //TODO: update slab info to remove the devices from slab_devices

    return true;
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


static slab_platformdevices_t __xmhfhic_arch_sda_get_devices_for_slab(u64 slabid, slab_platformdevices_t devices){
    slab_platformdevices_t retval;

    retval.desc_valid=false;
    retval.numdevices=0;

    /* x86_64
    //for now detect rich guest slab and allocate all platform devices to it
    if(_xmhfhic_common_slab_info_table[slabid].slab_devices.desc_valid &&
        _xmhfhic_common_slab_info_table[slabid].slab_devices.numdevices == 0xFFFFFFFFFFFFFFFFULL)
        return devices;
    else
        return retval;
    */

    //for now detect rich guest slab and allocate all platform devices to it
    if(_xmhfhic_common_slab_info_table[slabid].slab_devices.desc_valid &&
        _xmhfhic_common_slab_info_table[slabid].slab_devices.numdevices == 0xFFFFFFFFUL)
        return devices;
    else
        return retval;

}

void xmhfhic_arch_setup_slab_device_allocation(void){
    u32 i;
    slab_platformdevices_t ddescs;

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

    //intialize VT-d and enumerate system devices
    ddescs = __xmhfhic_arch_initializeandenumeratedevices();

    if(!ddescs.desc_valid){
        _XDPRINTF_("%s: Error: could not obtain platform device descriptors\n",
                    __func__);
        HALT();
    }

    for(i=0; i < ddescs.numdevices; i++){
        _XDPRINTF_("  %02x:%02x.%1x -> vendor_id=%04x, device_id=%04x\n", ddescs.arch_desc[i].pci_bus,
          ddescs.arch_desc[i].pci_device, ddescs.arch_desc[i].pci_function,
          ddescs.arch_desc[i].vendor_id, ddescs.arch_desc[i].device_id);
    }


    //TODO: for each slab, parse the list of devices allocated to it and allocate
    //the device to the slab
    for(i=0; i < XMHF_HIC_MAX_SLABS; i++){
        slab_platformdevices_t slab_ddescs;

        slab_ddescs = __xmhfhic_arch_sda_get_devices_for_slab(i, ddescs);

        if(slab_ddescs.desc_valid){
            _XDPRINTF_("%s: Allocating %u devices to slab %u...\n",
                            __func__, slab_ddescs.numdevices, i);


            if(!__xmhfhic_arch_sda_allocdevices_to_slab(i, slab_ddescs)){
                    _XDPRINTF_("%s: Halting.unable to allocate devices to slab %u\n",
                                __func__, i);
                    HALT();
            }
        }else{
            _XDPRINTF_("%s: No devices to allocate for slab %u...\n",
                            __func__, i);
        }
    }

}





















//////////////////////////////////////////////////////////////////////////////
// setup slab memory page tables (smt)


#define	_SLAB_SPATYPE_OTHER_SLAB_MASK			(0xF0)

#define	_SLAB_SPATYPE_OTHER_SLAB_CODE			(0xF0)
#define	_SLAB_SPATYPE_OTHER_SLAB_RWDATA			(0xF1)
#define _SLAB_SPATYPE_OTHER_SLAB_RODATA			(0xF2)
#define _SLAB_SPATYPE_OTHER_SLAB_STACK			(0xF3)
#define _SLAB_SPATYPE_OTHER_SLAB_DMADATA        (0xF4)

#define	_SLAB_SPATYPE_SLAB_CODE					(0x0)
#define	_SLAB_SPATYPE_SLAB_RWDATA				(0x1)
#define _SLAB_SPATYPE_SLAB_RODATA				(0x2)
#define _SLAB_SPATYPE_SLAB_STACK				(0x3)
#define _SLAB_SPATYPE_SLAB_DMADATA				(0x4)

#define _SLAB_SPATYPE_HIC           			(0x5)
#define _SLAB_SPATYPE_HIC_SHAREDRO     			(0x6)

#define _SLAB_SPATYPE_OTHER	    				(0xFF00)

static u32 __xmhfhic_hyp_slab_getspatype(u64 slab_index, u32 spa){
	u64 i;

	//slab memory regions
	for(i=0; i < XMHF_HIC_MAX_SLABS; i++){
		u64 mask = (i == slab_index) ? 0 : _SLAB_SPATYPE_OTHER_SLAB_MASK;

		if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[0].addr_end)
			return _SLAB_SPATYPE_SLAB_CODE | mask;
		if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[1].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[1].addr_end)
			return _SLAB_SPATYPE_SLAB_RWDATA | mask;
		//if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_end)
		//	return _SLAB_SPATYPE_SLAB_RODATA | mask;
		if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_end)
			return _SLAB_SPATYPE_SLAB_STACK | mask;
		if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[4].addr_end)
			return _SLAB_SPATYPE_SLAB_DMADATA | mask;
	}

	//HIC shared ro region
	//TODO: add per shared data variable access policy rather than entire section
	//if(spa >= _xmhfhic_common_hic_physmem_extents[0].addr_start && spa < _xmhfhic_common_hic_physmem_extents[0].addr_end)
	//	return _SLAB_SPATYPE_HIC_SHAREDRO;

	//HIC code,rodata,rwdat and stack
    //if(spa >= _xmhfhic_common_hic_physmem_extents[1].addr_start && spa < _xmhfhic_common_hic_physmem_extents[1].addr_end)
	//	return _SLAB_SPATYPE_HIC;
    //if(spa >= _xmhfhic_common_hic_physmem_extents[2].addr_start && spa < _xmhfhic_common_hic_physmem_extents[2].addr_end)
	//	return _SLAB_SPATYPE_HIC;
    //if(spa >= _xmhfhic_common_hic_physmem_extents[3].addr_start && spa < _xmhfhic_common_hic_physmem_extents[3].addr_end)
	//	return _SLAB_SPATYPE_HIC;
    //if(spa >= _xmhfhic_common_hic_physmem_extents[4].addr_start && spa < _xmhfhic_common_hic_physmem_extents[4].addr_end)
	//	return _SLAB_SPATYPE_HIC;


	return _SLAB_SPATYPE_OTHER;
}

static u64 __xmhfhic_hyp_slab_getptflagsforspa(u64 slabid, u32 spa){
	u64 flags;
	u32 spatype = __xmhfhic_hyp_slab_getspatype(slabid, spa);
	//_XDPRINTF_("\n%s: slab_index=%u, spa=%08x, spatype = %x\n", __func__, slab_index, spa, spatype);

	switch(spatype){
		case _SLAB_SPATYPE_OTHER_SLAB_CODE:
		case _SLAB_SPATYPE_OTHER_SLAB_RWDATA:
		case _SLAB_SPATYPE_OTHER_SLAB_RODATA:
		case _SLAB_SPATYPE_OTHER_SLAB_STACK:
		case _SLAB_SPATYPE_OTHER_SLAB_DMADATA:
			flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE);
			break;

		case _SLAB_SPATYPE_SLAB_CODE:
			flags = (u64)(_PAGE_PRESENT | _PAGE_PSE | _PAGE_USER);
			break;
		case _SLAB_SPATYPE_SLAB_RODATA:
			flags = (u64)(_PAGE_PRESENT | _PAGE_PSE | _PAGE_NX | _PAGE_USER);
			break;
		case _SLAB_SPATYPE_SLAB_RWDATA:
		case _SLAB_SPATYPE_SLAB_STACK:
		case _SLAB_SPATYPE_SLAB_DMADATA:
			flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_NX | _PAGE_PSE | _PAGE_USER);
			break;

		case _SLAB_SPATYPE_HIC_SHAREDRO:
            flags = (u64)(_PAGE_PRESENT | _PAGE_RW  | _PAGE_PSE | _PAGE_USER);
			break;

        case _SLAB_SPATYPE_HIC:
			flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE);
			break;


		default:
			flags = (u64)(_PAGE_PRESENT | _PAGE_RW | _PAGE_PSE | _PAGE_USER);
			if(spa == 0xfee00000 || spa == 0xfec00000) {
				//map some MMIO regions with Page Cache disabled
				//0xfed00000 contains Intel TXT config regs & TPM MMIO
				//0xfee00000 contains LAPIC base
				flags |= (u64)(_PAGE_PCD);
			}
			break;
	}


	return flags;
}

#if !defined (__XMHF_VERIFICATION__)
//
// initialize slab page tables for a given slab index, returns the macm base
static u64 __xmhfhic_arch_smt_slab_populate_hyp_pagetables(u64 slabid){
		u32 i, j;
		//u64 default_flags = (u64)(_PAGE_PRESENT) | (u64)(_PAGE_USER) | (u64)(_PAGE_RW);
        u64 default_flags = (u64)(_PAGE_PRESENT);

        //_dbuf_mempgtbl_pml4t/pdpt/pdt/pt[slabid] is the data backing for slabid

        /* x86_64
        for(i=0; i < PAE_PTRS_PER_PML4T; i++){
            _dbuf_mempgtbl_pml4t[slabid][i] = pae_make_pml4e(hva2spa(&_dbuf_mempgtbl_pdpt[slabid]), default_flags);
        }*/

		for(i=0; i < PAE_PTRS_PER_PDPT; i++){
			_dbuf_mempgtbl_pdpt[slabid][i] = pae_make_pdpe(hva2spa(&_dbuf_mempgtbl_pdt[slabid][i]), default_flags);
		}

		//init pdts with unity mappings
		for(i=0; i < PAE_PTRS_PER_PDPT; i++){
			for(j=0; j < PAE_PTRS_PER_PDT; j++){
				u32 hva = ((i * PAE_PTRS_PER_PDT) + j) * PAGE_SIZE_2M;
				u64 spa = hva2spa((void*)hva);
				u64 flags = __xmhfhic_hyp_slab_getptflagsforspa(slabid, (u32)spa);
				_dbuf_mempgtbl_pdt[slabid][i][j] = pae_make_pde_big(spa, flags);
			}
		}

        //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pml4t = (u64)&_dbuf_mempgtbl_pml4t[slabid];
        //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt = (u64)&_dbuf_mempgtbl_pdpt[slabid];
        //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdt = (u64)&_dbuf_mempgtbl_pdt[slabid];
        //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pt = (u64)&_dbuf_mempgtbl_pt[slabid]; //FIXME: we dont need this allocation


/*        for(i=0; i < PAE_PTRS_PER_PML4T; i++){
            //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pml4t[i] = pae_make_pml4e(hva2spa(&_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt), default_flags);
            _xmhfhic_common_slab_archdata_mempgtbl_pml4t[slabid][i] = pae_make_pml4e(hva2spa(&_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt), default_flags);
            //    if(slabid == 0){
            //        _XDPRINTF_("pml4t[%u] = %016llx\n", i, _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pml4t[i]);
            //    }
        }

		for(i=0; i < PAE_PTRS_PER_PDPT; i++){
			_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt[i] = pae_make_pdpe(hva2spa(_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdt[i]), default_flags);
            //    if(slabid == 0){
            //        _XDPRINTF_("pdpt[%u] = %016llx\n", i, _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt[i]);
            //    }
		}

		//init pdts with unity mappings
		for(i=0; i < PAE_PTRS_PER_PDPT; i++){
			for(j=0; j < PAE_PTRS_PER_PDT; j++){
				u32 hva = ((i * PAE_PTRS_PER_PDT) + j) * PAGE_SIZE_2M;
				u64 spa = hva2spa((void*)hva);
				u64 flags = __xmhfhic_hyp_slab_getptflagsforspa(slabid, (u32)spa);
				_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdt[i][j] = pae_make_pde_big(spa, flags);

                //if(slabid == 0){
                //    _XDPRINTF_("pdt[%u][%u] = %016llx\n", i, j, _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdt[i][j]);
                //}
			}
		}*/

        return (u64)&_dbuf_mempgtbl_pdpt[slabid];
		//return _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt;
		//return _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pml4t;
		//return _xmhfhic_common_slab_archdata_mempgtbl_pml4t[slabid];
}
#endif



static struct _memorytype _vmx_ept_memorytypes[MAX_MEMORYTYPE_ENTRIES]; //EPT memory types array

static void __xmhfhic_vmx_gathermemorytypes(void);
static u32 __xmhfhic_vmx_getmemorytypeforphysicalpage(u64 pagebaseaddr);
static void __xmhfhic_vmx_setupEPT(u64 guestslab_id);

#if !defined (__XMHF_VERIFICATION__)
static void __xmhfhic_guestpgtbl_setentry(u64 slabid,  u64 gpa, u64 entry){
    u64 pdpt_index = pae_get_pdpt_index(gpa);
    u64 pd_index = pae_get_pdt_index(gpa);
    u64 pt_index = pae_get_pt_index(gpa);

    //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pt[pdpt_index][pd_index][pt_index] = entry;
    //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pt[(gpa/PAGE_SIZE_4K)]= entry;

    _dbuf_mempgtbl_pt[slabid][pdpt_index][pd_index][pt_index] = entry;
	return;
}
#endif

#if !defined (__XMHF_VERIFICATION__)
static void __xmhfhic_guestpgtbl_establishshape(u64 slabid){
	u32 i, j;

    //_dbuf_mempgtbl_pml4t/pdpt/pdt/pt[slabid] is the data backing for slabid

    for(i=0; i < PAE_PTRS_PER_PML4T; i++)
        _dbuf_mempgtbl_pml4t[slabid][i] = (u64) (hva2spa((void*)&_dbuf_mempgtbl_pdpt[slabid]) | 0x7);

	for(i=0; i < PAE_PTRS_PER_PDPT; i++)
		_dbuf_mempgtbl_pdpt[slabid][i] = (u64) ( hva2spa((void*)&_dbuf_mempgtbl_pdt[slabid][i]) | 0x7 );

	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			_dbuf_mempgtbl_pdt[slabid][i][j] = (u64) ( hva2spa((void*)&_dbuf_mempgtbl_pt[slabid][i][j]) | 0x7 );
		}
	}


/*    for(i=0; i < PAE_PTRS_PER_PML4T; i++)
        //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pml4t[i] = (u64) (hva2spa((void*)_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt) | 0x7);
        _xmhfhic_common_slab_archdata_mempgtbl_pml4t[slabid][i] = (u64) (hva2spa((void*)_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt) | 0x7);

	for(i=0; i < PAE_PTRS_PER_PDPT; i++)
		_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt[i] = (u64) ( hva2spa((void*)_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdt[i]) | 0x7 );

	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdt[i][j] = (u64) ( hva2spa((void*)_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pt[i][j]) | 0x7 );
		}
	}*/


    //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pml4t = (u64)&_dbuf_mempgtbl_pml4t[slabid];
    //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt = (u64)&_dbuf_mempgtbl_pdpt[slabid];
    //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdt = (u64)&_dbuf_mempgtbl_pdt[slabid];
    //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pt = (u64)&_dbuf_mempgtbl_pt[slabid]; //FIXME: we dont need this allocation


}
#endif


//---gather memory types for system physical memory------------------------------
static void __xmhfhic_vmx_gathermemorytypes(void){
 	u32 eax, ebx, ecx, edx;
	u32 index=0;
	u32 num_vmtrrs=0;	//number of variable length MTRRs supported by the CPU

	//0. sanity check
  	//check MTRR support
  	eax=0x00000001;
  	ecx=0x00000000;
	/*#ifndef __XMHF_VERIFICATION__
  	asm volatile ("cpuid\r\n"
            :"=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
            :"a"(eax), "c" (ecx));
  	#endif*/
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
static u32 __xmhfhic_vmx_getmemorytypeforphysicalpage(u64 pagebaseaddr){
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


//---setup EPT for VMX----------------------------------------------------------
static void __xmhfhic_vmx_setupEPT(u64 slabid){
	u64 p_table_value;
	u64 gpa;
    //slab_retval_t srval;

	for(gpa=0; gpa < ADDR_4GB; gpa += PAGE_SIZE_4K){
		u32 memorytype = __xmhfhic_vmx_getmemorytypeforphysicalpage((u64)gpa);
		//make XMHF physical pages inaccessible
		//if( (gpa >= (__TARGET_BASE_XMHF)) &&
		//	(gpa < (__TARGET_BASE_XMHF + __TARGET_SIZE_XMHF)) ){
		//	p_table_value = (u64) (gpa)  | ((u64)memorytype << 3) | (u64)0x0 ;	//not-present
		//}else{
			if(memorytype == 0)
				p_table_value = (u64) (gpa)  | ((u64)memorytype << 3) |  (u64)0x7 ;	//present, UC
			else
				p_table_value = (u64) (gpa)  | ((u64)6 << 3) | (u64)0x7 ;	//present, WB, track host MTRR
		//}

        __xmhfhic_guestpgtbl_setentry(slabid, gpa, p_table_value);

	}
}


static u64 __xmhfhic_arch_smt_slab_populate_guest_pagetables(u64 slabid){

    __xmhfhic_guestpgtbl_establishshape(slabid);

	__xmhfhic_vmx_setupEPT(slabid);

    return &_dbuf_mempgtbl_pml4t[slabid];
    //return _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pml4t;
    //return _xmhfhic_common_slab_archdata_mempgtbl_pml4t[slabid];
}


void xmhfhic_arch_setup_slab_mem_page_tables(void){

	_XDPRINTF_("%s: starting...\n", __func__);

    //gather memory types for EPT (for guest slabs)
    __xmhfhic_vmx_gathermemorytypes();

	//setup slab memory page tables
	{
		u32 i;
		for(i=0; i < XMHF_HIC_MAX_SLABS; i++){
				//_XDPRINTF_("slab %u: pml4t=%016llx, pdpt=%016llx, pdt[0]=%016llx, pdt[1]=%016llx, pdt[2]=%016llx, pdt[3]=%016llx\n", i,
                //    _xmhfhic_common_slab_archdata_mempgtbl_pml4t[i],
                //    _xmhfhic_common_slab_info_table[i].archdata.mempgtbl_pdpt,
                //    _xmhfhic_common_slab_info_table[i].archdata.mempgtbl_pdt[0],
                //    _xmhfhic_common_slab_info_table[i].archdata.mempgtbl_pdt[1],
                //    _xmhfhic_common_slab_info_table[i].archdata.mempgtbl_pdt[2],
                //    _xmhfhic_common_slab_info_table[i].archdata.mempgtbl_pdt[3]
               //);

                switch(_xmhfhic_common_slab_info_table[i].archdata.slabtype){
                    case HIC_SLAB_X86VMXX86PC_HYPERVISOR:{
                        _XDPRINTF_("  HYPERVISOR slab: populating page tables\n");

                        #if 0
                        _xmhfhic_common_slab_info_table[i].archdata.mempgtbl_cr3 = __xmhfhic_arch_smt_slab_populate_hyp_pagetables(i) | (u32)(i+1) | 0x8000000000000000ULL;
                        #else
                        _xmhfhic_common_slab_info_table[i].archdata.mempgtbl_cr3 = __xmhfhic_arch_smt_slab_populate_hyp_pagetables(i);
                        #endif
                    }
                    break;

                    case HIC_SLAB_X86VMXX86PC_GUEST:{
                        _XDPRINTF_("  GUEST slab: populating page tables\n");

                        _xmhfhic_common_slab_info_table[i].archdata.mempgtbl_cr3 = __xmhfhic_arch_smt_slab_populate_guest_pagetables(i) | 0x1E;
                    }
                    break;

                    default: //unallocated slab or an unknown slabtype
                        break;
                }

		}

	}

	_XDPRINTF_("%s: setup slab memory page tables\n", __func__);

}




















































































#if 0

    //debug
    _XDPRINTF_("Halting!\n");
    _XDPRINTF_("XMHF Tester Finished!\n");
    HALT();

#endif // 0
