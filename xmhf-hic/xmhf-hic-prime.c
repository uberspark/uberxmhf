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

//external assembly language blobs
extern void _ap_bootstrap_code(void);
extern bool __xmhfhic_ap_entry(void);
extern void xmhfhic_arch_relinquish_control_to_init_slab(u64 cpuid, u64 entrystub, u64 mempgtbl_cr3, u64 slabtos);
extern void __xmhfhic_x86vmx_setIOPL3(u64 cpuid);
extern void __xmhfhic_x86vmx_loadTR(u64 cpuid);
extern void __xmhfhic_x86vmx_loadIDT(arch_x86_idtdesc_t *idt_addr);
extern void __xmhfhic_x86vmx_loadGDT(arch_x86_gdtdesc_t *gdt_addr);






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
        _XDPRINTF_("fn:%s, line:%u\n", __FUNCTION__, __LINE__);
        wrmsr64(MSR_EFER, (rdmsr64(MSR_EFER) | (0x800)) );
        _XDPRINTF_("EFER=%016llx\n", rdmsr64(MSR_EFER));
        write_cr4(read_cr4() | (0x30) );
        _XDPRINTF_("CR4=%08x\n", read_cr4());
        write_cr3((u32)&_xcprimeon_init_pdpt);
        _XDPRINTF_("CR3=%08x\n", read_cr3());
        write_cr0(0x80000015);
        _XDPRINTF_("fn:%s, line:%u\n", __FUNCTION__, __LINE__);
    }

}











void slab_main(slab_params_t *sp){
    u64 pgtblbase;

#if !defined(__XMHF_VERIFICATION__)
	//initialize debugging early on
	xmhfhw_platform_serial_init((char *)&xcbootinfo->debugcontrol_buffer);


	//[debug] print relevant startup info.
	_XDPRINTF_("%s: alive and starting...\n", __FUNCTION__);

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

    HALT();

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

    //setup base CPU data structures
    xmhfhic_arch_setup_base_cpu_data_structures();

    //setup SMP and move on to xmhfhic_smp_entry
    xmhfhic_arch_switch_to_smp();

    //we should never get here
    _XDPRINTF_("Should never be here. Halting!\n");
    HALT();
}


void xmhfhic_smp_entry(u32 cpuid){
    bool isbsp = (cpuid & 0x80000000UL) ? true : false;
    #if defined (__XMHF_VERIFICATION__)
    cpuid = 0;
    isbsp = true;
    #endif // defined


    //[debug] halt all APs
    //if(!isbsp){
    //    _XDPRINTF_("%s[%u,%u]: esp=%08x. AP Halting!\n",
    //        __FUNCTION__, (u16)cpuid, isbsp, read_esp());
    //    HALT();
    //}

    _XDPRINTF_("%s[%u,%u]: esp=%08x. Starting...\n",
            __FUNCTION__, cpuid, isbsp, read_esp());

    xmhf_hic_arch_setup_cpu_state((u16)cpuid);

    //_XDPRINTF_("%s[%u,%u]: Halting!\n", __FUNCTION__, (u16)cpuid, isbsp);
    //HALT();


    //relinquish HIC initialization and move on to the first slab
    _XDPRINTF_("%s[%u]: proceeding to call init slab at %x\n", __FUNCTION__, (u16)cpuid,
                _xmhfhic_common_slab_info_table[XMHF_HYP_SLAB_XCINIT].entrystub);

    //xmhfhic_arch_relinquish_control_to_init_slab(cpuid,
    //    _xmhfhic_common_slab_info_table[XMHF_HYP_SLAB_XCINIT].entrystub,
    //    _xmhfhic_common_slab_info_table[XMHF_HYP_SLAB_XCINIT].archdata.mempgtbl_cr3,
    //    _xmhfhic_common_slab_info_table[XMHF_HYP_SLAB_XCINIT].archdata.slabtos[(u32)cpuid]);

    {
        slab_params_t sp;

        memset(&sp, 0, sizeof(sp));
        sp.cpuid = cpuid;
        sp.dst_slabid = XMHF_HYP_SLAB_XCINIT;
        XMHF_SLAB_CALLNEW(&sp);
    }


    _XDPRINTF_("%s[%u,%u]: Should never be here. Halting!\n", __FUNCTION__, (u16)cpuid, isbsp);
    HALT();

}



//////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////
// setup slab info

void xmhfhic_arch_setup_slab_info(void){

    //initialize slab info table
    {
        u32 i;

        for(i=0; i < XMHF_HIC_MAX_SLABS; i++){

            _xmhfhic_common_slab_info_table[i].slab_inuse = true;
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

            #if !defined(__XMHF_VERIFICATION__)
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

        }
    }


    #if !defined (__XMHF_VERIFICATION__)
    //initialize HIC physical memory extents
    memcpy(_xmhfhic_common_hic_physmem_extents,
           _xmhfhic_init_setupdata_hic_physmem_extents,
           sizeof(_xmhfhic_common_hic_physmem_extents));
    #endif

    #if !defined (__XMHF_VERIFICATION__)
	//print out HIC section information
    {
		_XDPRINTF_("xmhfhic section info:\n");
		_XDPRINTF_("  xmhfhic sharedro(%08x-%08x)\n", _xmhfhic_common_hic_physmem_extents[0].addr_start, _xmhfhic_common_hic_physmem_extents[0].addr_end);
		_XDPRINTF_("  xmhfhic code(%08x-%08x)\n", _xmhfhic_common_hic_physmem_extents[1].addr_start, _xmhfhic_common_hic_physmem_extents[1].addr_end);
		_XDPRINTF_("  xmhfhic rwdata(%08x-%08x)\n", _xmhfhic_common_hic_physmem_extents[2].addr_start, _xmhfhic_common_hic_physmem_extents[2].addr_end);
		_XDPRINTF_("  xmhfhic rodata(%08x-%08x)\n", _xmhfhic_common_hic_physmem_extents[3].addr_start, _xmhfhic_common_hic_physmem_extents[3].addr_end);
		_XDPRINTF_("  xmhfhic stack(%08x-%08x)\n", _xmhfhic_common_hic_physmem_extents[4].addr_start, _xmhfhic_common_hic_physmem_extents[4].addr_end);

    }

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
		_XDPRINTF_("%s: not an Intel CPU but running VMX backend. Halting!\n", __FUNCTION__);
		HALT();
	}

	//check VMX support
	{
		u32	cpu_features;
		u32 res0,res1,res2;

		xmhfhw_cpu_cpuid(0x1, &res0, &res1, &cpu_features, &res2);

		if ( ( cpu_features & (1<<5) ) == 0 ){
			_XDPRINTF_("No VMX support. Halting!\n");
			HALT();
		}
	}

	//we require unrestricted guest and EPT support, bail out if we don't have it
    {
        u64 msr_procctls2 = rdmsr64(IA32_VMX_PROCBASED_CTLS2_MSR);
        if( !( (msr_procctls2 >> 32) & 0x80 ) ){
            _XDPRINTF_("%s: need unrestricted guest support but did not find any!\n", __FUNCTION__);
            HALT();
        }

        if( !( (msr_procctls2 >> 32) & 0x2) ){
            _XDPRINTF_("%s: need EPTt support but did not find any!\n", __FUNCTION__);
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
        _vtd_ret[i].qwords[0] = _vtd_ret[i].qwords[1] = 0ULL;
        _vtd_ret[i].fields.p = 1;
        _vtd_ret[i].fields.ctp = ((u64)&_vtd_cet[i] >> 12);

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
        _XDPRINTF_("%s: unable to scan for DRHD units. bailing out!\n", __FUNCTION__);
		return false;
	}

    _XDPRINTF_("%s: maxhandle = %u, dmar table addr=0x%08x\n", __FUNCTION__,
                (u32)vtd_drhd_maxhandle, (u32)vtd_dmar_table_physical_address);



	//initialize all DRHD units
	for(drhd_handle=0; drhd_handle < vtd_drhd_maxhandle; drhd_handle++){
   		VTD_CAP_REG cap;

		_XDPRINTF_("%s: Setting up DRHD unit %u...\n", __FUNCTION__, drhd_handle);

		if(!xmhfhw_platform_x86pc_vtd_drhd_initialize(drhd_handle) ){
            _XDPRINTF_("%s: error setting up DRHD unit %u. bailing out!\n", __FUNCTION__, drhd_handle);
			return false;
		}

        //read and store DRHD supported page-walk length
        cap.value = xmhfhw_platform_x86pc_vtd_drhd_reg_read(drhd_handle, VTD_CAP_REG_OFF);
        if(cap.bits.sagaw & 0x2){
            if(vtd_pagewalk_level == VTD_PAGEWALK_NONE || vtd_pagewalk_level == VTD_PAGEWALK_3LEVEL){
                vtd_pagewalk_level = VTD_PAGEWALK_3LEVEL;
                _XDPRINTF_("%s: DRHD unit %u - 3-level page-walk\n", __FUNCTION__, drhd_handle);
            }else{
                _XDPRINTF_("%s: Halting: mixed hardware supported page-walk lengths\n",
                            __FUNCTION__);
                HALT();
            }
        }

        if(cap.bits.sagaw & 0x4){
            if(vtd_pagewalk_level == VTD_PAGEWALK_NONE || vtd_pagewalk_level == VTD_PAGEWALK_4LEVEL){
                vtd_pagewalk_level = VTD_PAGEWALK_4LEVEL;
                _XDPRINTF_("%s: DRHD unit %u - 4-level page-walk\n", __FUNCTION__, drhd_handle);
            }else{
                _XDPRINTF_("%s: Halting: mixed hardware supported page-walk lengths\n",
                            __FUNCTION__);
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

		_XDPRINTF_("%s: Successfully setup DRHD unit %u\n", __FUNCTION__, drhd_handle);
	}

	//zap VT-d presence in ACPI table...
	//TODO: we need to be a little elegant here. eventually need to setup
	//EPT/NPTs such that the DMAR pages are unmapped for the guest
	xmhfhw_sysmemaccess_writeu32(vtd_dmar_table_physical_address, 0UL);


    _XDPRINTF_("%s: final page-walk level=%u\n", __FUNCTION__, vtd_pagewalk_level);

    vtd_initialized = true;

    return true;
}

#if !defined (__XMHF_VERIFICATION__)
static vtd_slpgtbl_handle_t _platform_x86pc_vtd_setup_slpgtbl(u32 slabid){
    vtd_slpgtbl_handle_t retval = {0, 0};
    u32 i, j, k, paddr=0;

    //sanity check partition index
    if(slabid > XMHF_HIC_MAX_SLABS){
        _XDPRINTF_("%s: Error: slabid (%u) > XMHF_HIC_MAX_SLABS(%u). bailing out!\n", __FUNCTION__, slabid, XMHF_HIC_MAX_SLABS);
        return retval;
    }


    //setup device memory access for the partition
    _dbuf_devpgtbl[slabid].pml4t[0].fields.r = 1;
    _dbuf_devpgtbl[slabid].pml4t[0].fields.w = 1;
    _dbuf_devpgtbl[slabid].pml4t[0].fields.slpdpt =
        ((u64)_dbuf_devpgtbl[slabid].pdpt >> 12);

    for(i=0; i < PAE_PTRS_PER_PDPT; i++){
        _dbuf_devpgtbl[slabid].pdpt[i].fields.r = 1;
        _dbuf_devpgtbl[slabid].pdpt[i].fields.w = 1;
        _dbuf_devpgtbl[slabid].pdpt[i].fields.slpdt =
            ((u64)_dbuf_devpgtbl[slabid].pdt[i] >> 12);

        for(j=0; j < PAE_PTRS_PER_PDT; j++){
            _dbuf_devpgtbl[slabid].pdt[i][j].fields.r = 1;
            _dbuf_devpgtbl[slabid].pdt[i][j].fields.w = 1;
            _dbuf_devpgtbl[slabid].pdt[i][j].fields.slpt =
                ((u64)_dbuf_devpgtbl[slabid].pt[i][j] >> 12);

            for(k=0; k < PAE_PTRS_PER_PT; k++){
                _dbuf_devpgtbl[slabid].pt[i][j][k].fields.r = 1;
                _dbuf_devpgtbl[slabid].pt[i][j][k].fields.w = 1;
                _dbuf_devpgtbl[slabid].pt[i][j][k].fields.pageaddr = ((u64)paddr >> 12);
                paddr += PAGE_SIZE_4K;
            }
        }
    }

    //populate device page tables pml4t, pdpt, pdt and pt pointers in slab info table
    _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_pml4t = &_dbuf_devpgtbl[slabid].pml4t;
    _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_pdpt = &_dbuf_devpgtbl[slabid].pdpt;
    _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_pdt = &_dbuf_devpgtbl[slabid].pdt;
    _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_pt = &_dbuf_devpgtbl[slabid].pt;



    /*//setup device memory access for the partition
    _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pml4t[0].fields.r = 1;
    _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pml4t[0].fields.w = 1;
    _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pml4t[0].fields.slpdpt = ((u64)&_xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pdpt >> 12);

    for(i=0; i < PAE_PTRS_PER_PDPT; i++){
        _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pdpt[i].fields.r = 1;
        _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pdpt[i].fields.w = 1;
        _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pdpt[i].fields.slpdt = ((u64)&_xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pdt[i] >> 12);

        for(j=0; j < PAE_PTRS_PER_PDT; j++){
            _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pdt[i][j].fields.r = 1;
            _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pdt[i][j].fields.w = 1;
            _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pdt[i][j].fields.slpt = ((u64)&_xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pt[i][j] >> 12);

            for(k=0; k < PAE_PTRS_PER_PT; k++){
                _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pt[i][j][k].fields.r = 1;
                _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pt[i][j][k].fields.w = 1;
                _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl.pt[i][j][k].fields.pageaddr = ((u64)paddr >> 12);
                paddr += PAGE_SIZE_4K;
            }
        }
    }*/

    retval.addr_vtd_pml4t = _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_pml4t;
    retval.addr_vtd_pdpt = _xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_pdpt;

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
            _XDPRINTF_("%s: unable to initialize vt-d pagetables for slab %u\n", __FUNCTION__, slabid);
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
        #if !defined(__XMHF_VERIFICATION__)
        if(vtd_pagewalk_level == VTD_PAGEWALK_4LEVEL){
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.slptptr = ((u64)_xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_pml4t >> 12);
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.aw = 2; //4-level
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.did = (slabid + 1); //domain
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.p = 1; //present
        }else if (vtd_pagewalk_level == VTD_PAGEWALK_3LEVEL){
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.slptptr = ((u64)_xmhfhic_common_slab_info_table[slabid].archdata.devpgtbl_pdpt >> 12);
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.aw = 1; //3-level
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.did = (slabid + 1); //domain
            _vtd_cet[b][((d*PCI_FUNCTION_MAX) + f)].fields.p = 1; //present
        }else{ //unknown page walk length, fail
            return false;
        }
        #endif
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
			_XDPRINTF_("%s: ACPI RSDP not found, Halting!\n", __FUNCTION__);
			HALT();
		}
	}

    //intialize VT-d and enumerate system devices
    ddescs = __xmhfhic_arch_initializeandenumeratedevices();

    if(!ddescs.desc_valid){
        _XDPRINTF_("%s: Error: could not obtain platform device descriptors\n",
                    __FUNCTION__);
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
                            __FUNCTION__, slab_ddescs.numdevices, i);


            if(!__xmhfhic_arch_sda_allocdevices_to_slab(i, slab_ddescs)){
                    _XDPRINTF_("%s: Halting.unable to allocate devices to slab %u\n",
                                __FUNCTION__, i);
                    HALT();
            }
        }else{
            _XDPRINTF_("%s: No devices to allocate for slab %u...\n",
                            __FUNCTION__, i);
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
		if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[2].addr_end)
			return _SLAB_SPATYPE_SLAB_RODATA | mask;
		if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[3].addr_end)
			return _SLAB_SPATYPE_SLAB_STACK | mask;
		if(spa >= _xmhfhic_common_slab_info_table[i].slab_physmem_extents[4].addr_start && spa < _xmhfhic_common_slab_info_table[i].slab_physmem_extents[4].addr_end)
			return _SLAB_SPATYPE_SLAB_DMADATA | mask;
	}

	//HIC shared ro region
	//TODO: add per shared data variable access policy rather than entire section
	if(spa >= _xmhfhic_common_hic_physmem_extents[0].addr_start && spa < _xmhfhic_common_hic_physmem_extents[0].addr_end)
		return _SLAB_SPATYPE_HIC_SHAREDRO;

	//HIC code,rodata,rwdat and stack
    if(spa >= _xmhfhic_common_hic_physmem_extents[1].addr_start && spa < _xmhfhic_common_hic_physmem_extents[1].addr_end)
		return _SLAB_SPATYPE_HIC;
    if(spa >= _xmhfhic_common_hic_physmem_extents[2].addr_start && spa < _xmhfhic_common_hic_physmem_extents[2].addr_end)
		return _SLAB_SPATYPE_HIC;
    if(spa >= _xmhfhic_common_hic_physmem_extents[3].addr_start && spa < _xmhfhic_common_hic_physmem_extents[3].addr_end)
		return _SLAB_SPATYPE_HIC;
    if(spa >= _xmhfhic_common_hic_physmem_extents[4].addr_start && spa < _xmhfhic_common_hic_physmem_extents[4].addr_end)
		return _SLAB_SPATYPE_HIC;


	return _SLAB_SPATYPE_OTHER;
}

static u64 __xmhfhic_hyp_slab_getptflagsforspa(u64 slabid, u32 spa){
	u64 flags;
	u32 spatype = __xmhfhic_hyp_slab_getspatype(slabid, spa);
	//_XDPRINTF_("\n%s: slab_index=%u, spa=%08x, spatype = %x\n", __FUNCTION__, slab_index, spa, spatype);

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
        _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt = (u64)&_dbuf_mempgtbl_pdpt[slabid];
        _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdt = (u64)&_dbuf_mempgtbl_pdt[slabid];
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

		return _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt;
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
    //u64 pdpt_index = pae_get_pdpt_index(gpa);
    //u64 pd_index = pae_get_pdt_index(gpa);
    //u64 pt_index = pae_get_pt_index(gpa);

    //_xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pt[pdpt_index][pd_index][pt_index] = entry;
    _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pt[(gpa/PAGE_SIZE_4K)]= entry;

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


    _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pml4t = (u64)&_dbuf_mempgtbl_pml4t[slabid];
    _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdpt = (u64)&_dbuf_mempgtbl_pdpt[slabid];
    _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pdt = (u64)&_dbuf_mempgtbl_pdt[slabid];
    _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pt = (u64)&_dbuf_mempgtbl_pt[slabid]; //FIXME: we dont need this allocation


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
  	xmhfhw_cpu_cpuid(0x00000001, &eax, &ebx, &ecx, &edx);

  	if( !(edx & (u32)(1 << 12)) ){
  		_XDPRINTF_("\n%s: CPU does not support MTRRs!", __FUNCTION__);
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

	_XDPRINTF_("\n%s: gathered MTRR details, number of entries=%u", __FUNCTION__, index);
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

    _XDPRINTF_("\n%s: endaddr < 1M and unmatched fixed MTRR. Halt!", __FUNCTION__);
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

    return _xmhfhic_common_slab_info_table[slabid].archdata.mempgtbl_pml4t;
    //return _xmhfhic_common_slab_archdata_mempgtbl_pml4t[slabid];
}


void xmhfhic_arch_setup_slab_mem_page_tables(void){

	_XDPRINTF_("%s: starting...\n", __FUNCTION__);

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

	_XDPRINTF_("%s: setup slab memory page tables\n", __FUNCTION__);

}































//////////////////////////////////////////////////////////////////////////////
// switch to smp

//static bool __xmhfhic_ap_entry(void) __attribute__((naked));
void __xmhfhic_smp_cpu_x86_smpinitialize_commonstart(void);
static u64 _xcsmp_ap_entry_lock = 1;
static mtrr_state_t _mtrrs;
u64 _ap_cr3=0;




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

    apdata.ap_cr3 = read_cr3();
    apdata.ap_cr4 = read_cr4();
    apdata.ap_entrypoint = (u32)&__xmhfhic_ap_entry;
    apdata.ap_gdtdesc_limit = sizeof(apdata.ap_gdt) - 1;
    apdata.ap_gdtdesc_base = (X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_gdt);
    apdata.ap_cs_selector = __CS_CPL0;
    apdata.ap_eip = (X86SMP_APBOOTSTRAP_CODESEG << 4);
    apdata.cpuidtable = (u32)&__xmhfhic_x86vmx_cpuidtable;
    apdata.ap_gdt[0] = 0x0000000000000000ULL;
    apdata.ap_gdt[1] = 0x00cf9a000000ffffULL;
    apdata.ap_gdt[2] = 0x00cf92000000ffffULL;

    _XDPRINTF_("%s: sizeof(apdata)=%u bytes\n", __FUNCTION__, sizeof(apdata));
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

        mle_join = (mle_join_t *)((u32)(X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_gdtdesc_limit));

        _XDPRINTF_("\nBSP: mle_join.gdt_limit = %x", mle_join->gdt_limit);
        _XDPRINTF_("\nBSP: mle_join.gdt_base = %x", mle_join->gdt_base);
        _XDPRINTF_("\nBSP: mle_join.seg_sel = %x", mle_join->seg_sel);
        _XDPRINTF_("\nBSP: mle_join.entry_point = %x", mle_join->entry_point);

        write_priv_config_reg(TXTCR_MLE_JOIN, (uint64_t)(unsigned long)mle_join);

        if (os_sinit_data->capabilities.rlp_wake_monitor) {
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
    _ap_cr3 = read_cr3();

	//wake up APS
	if(xcbootinfo->cpuinfo_numentries > 1){
	  __xmhfhic_smp_container_vmx_wakeupAPs();
	}

	//fall through to common code
	_XDPRINTF_("%s: Relinquishing BSP thread and moving to common...\n", __FUNCTION__);
	__xmhfhic_smp_cpu_x86_smpinitialize_commonstart();

	_XDPRINTF_("%s:%u: Must never get here. Halting\n", __FUNCTION__, __LINE__);
	HALT();

}

//return 1 if the calling CPU is the BSP
static bool __xmhfhic_smp_cpu_x86_isbsp(void){
  u32 eax, edx;
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G

  if(eax & 0x100)
    return true;
  else
    return false;
}


//common function which is entered by all CPUs upon SMP initialization
//note: this is specific to the x86 architecture backend
void __xmhfhic_smp_cpu_x86_smpinitialize_commonstart(void){
	u32 cpuid;
	#if !defined(__XMHF_VERIFICATION__)
	cpuid  = __xmhfhic_x86vmx_cpuidtable[xmhf_baseplatform_arch_x86_getcpulapicid()];
    #endif

    xmhfhic_smp_entry(cpuid);
}





void xmhfhic_arch_switch_to_smp(void){
	//initialize cpu table and total platform CPUs
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
	}

    __xmhfhic_smp_arch_smpinitialize();

}























/////////////////////////////////////////////////////////////////////
// setup base CPU data structures

//initialize GDT
static void __xmhfhic_x86vmx_initializeGDT(void){
		u32 i;

		for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
            TSSENTRY *t;
            u32 tss_base=(u32)&__xmhfhic_x86vmx_tss[i];

            //TSS descriptor
            t= (TSSENTRY *)&__xmhfhic_x86vmx_gdt_start[(__TRSEL/8)+(i*2)];
            t->attributes1= 0xE9;
            t->limit16_19attributes2= 0x0;
            t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
            t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
            t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);
            t->limit0_15=0x67;
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
            tss_t *tss= (tss_t *)__xmhfhic_x86vmx_tss[i];
            /* x86_64
            tss->rsp0 = (u64) ( &__xmhfhic_x86vmx_tss_stack[i] + sizeof(__xmhfhic_x86vmx_tss_stack[0]) );
            */
            tss->esp0 = (u32) ( &__xmhfhic_x86vmx_tss_stack[i] + sizeof(__xmhfhic_x86vmx_tss_stack[0]) );
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

    write_cr4( read_cr4() |  CR4_VMXE);

#if !defined (__XMHF_VERIFICATION__)
	//enter VMX root operation using VMXON
	{
		u32 retval=0;
		u64 vmxonregion_paddr = hva2spa((void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmxon_region);
		//set VMCS rev id
		*((u32 *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmxon_region) = (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

        if(!__vmx_vmxon(vmxonregion_paddr)){
			_XDPRINTF_("%s(%u): unable to enter VMX root operation\n", __FUNCTION__, (u32)cpuid);
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
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR0, read_cr0());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR4, read_cr4());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CR3, read_cr3());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_CS_SELECTOR, read_segreg_cs());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_DS_SELECTOR, read_segreg_ds());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_ES_SELECTOR, read_segreg_es());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_FS_SELECTOR, read_segreg_fs());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GS_SELECTOR, read_segreg_gs());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SS_SELECTOR, read_segreg_ss());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_TR_SELECTOR, read_tr_sel());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GDTR_BASE, xmhf_baseplatform_arch_x86_getgdtbase());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_IDTR_BASE, xmhf_baseplatform_arch_x86_getidtbase());
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_TR_BASE, xmhf_baseplatform_arch_x86_gettssbase());

	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_RIP, __xmhfhic_rtm_intercept_stub);

	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_RSP, read_rsp());
	rdmsr(IA32_SYSENTER_CS_MSR, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_CS, lodword);
	rdmsr(IA32_SYSENTER_ESP_MSR, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_ESP, (((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_SYSENTER_EIP_MSR, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_SYSENTER_EIP, (((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_MSR_FS_BASE, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_FS_BASE, (((u64)hidword << 32) | (u64)lodword) );
	rdmsr(IA32_MSR_GS_BASE, &lodword, &hidword);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_HOST_GS_BASE, (((u64)hidword << 32) | (u64)lodword) );

	//setup default VMX controls
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_CONTROLS, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);

    /*
    x86_64
    //64-bit host
  	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_CONTROLS, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_EXIT_CONTROLS) | (1 << 9)) );
    */

	//IO bitmap support
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_iobitmap_region[0]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_iobitmap_region[1]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 25)) );

	//MSR bitmap support
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_MSR_BITMAPS_ADDRESS_FULL, hva2spa(__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrbitmaps_region ));
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 28)) );


	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_PAGEFAULT_ERRORCODE_MASK, 0x00000000);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_PAGEFAULT_ERRORCODE_MATCH, 0x00000000);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EXCEPTION_BITMAP, 0);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR3_TARGET_COUNT, 0);

	//activate secondary processor controls
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (u32) (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 31)) );

	//setup unrestricted guest
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 << 7)) );

	//setup VMCS link pointer
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_VMCS_LINK_POINTER_FULL, 0xFFFFFFFFUL);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_VMCS_LINK_POINTER_HIGH, 0xFFFFFFFFUL);

	//setup NMI intercept for core-quiescing
	//XXX: needs to go in xcinit/richguest slab
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_PIN_BASED) | (u64)(1 << 3) ) );

	//trap access to CR0 fixed 1-bits
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_MASK, (u32)(((((u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR] & ~(CR0_PE)) & ~(CR0_PG)) | CR0_CD) | CR0_NW) );

	//trap access to CR4 fixed bits (this includes the VMXE bit)
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR4_MASK, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR4_SHADOW, (u64)CR4_VMXE);

	//setup memory protection
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_SECCPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 <<1) | (u64)(1 << 5)) );
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VPID, 0); //[need to populate in trampoline]
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_FULL, 0); // [need to populate in trampoline]
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_EPT_POINTER_HIGH, 0); // [need to populate in trampoline]
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) & (u64)~(1 << 15) & (u64)~(1 << 16)) );

	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR0, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR]);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_SHADOW, xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0));

	xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);

	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_EXCEPTION_ERRORCODE, 0);
	xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_INTERRUPTION_INFORMATION, 0);


    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RSP, 0); //[need to populate in trampoline]

    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RIP, 0); // [need to populate in trampoline]
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ACTIVITY_STATE, 0);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_RFLAGS, (1 <<1) | (EFLAGS_IOPL));
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_INTERRUPTIBILITY, 0);


    //IDTR
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IDTR_BASE, 0);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IDTR_LIMIT, 0);



    //LDTR, unusable
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_BASE, 0);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_LIMIT, 0);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_SELECTOR, 0);
    xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_LDTR_ACCESS_RIGHTS, 0x10000);



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
                        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_IA32_EFER_FULL, gmsr[i].data);

                    }
                    break;

                    default:
                        break;
                }

            }

            //host MSR load on exit, we store it ourselves before entry
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, hva2spa((void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region));
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

            //guest MSR load on entry, store on exit
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, hva2spa((void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region));
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, hva2spa((void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region));
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);

        }


        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4) | CR4_PAE | CR4_PSE) );

        xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 9)) );
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 15)) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE0_FULL, _guestslab1_init_pdpt[0] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE1_FULL, _guestslab1_init_pdpt[1] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE2_FULL, _guestslab1_init_pdpt[2] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE3_FULL, _guestslab1_init_pdpt[3] );


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, &_guestslab1_init_pml4t );


        //TR, should be usable for VMX to work, but not used by guest
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_LIMIT, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_SELECTOR, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_ACCESS_RIGHTS, 0x8B);

        //CS, DS, ES, FS, GS and SS segments
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_SELECTOR, 0x8);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_LIMIT, 0xFFFFFFFFUL);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_ACCESS_RIGHTS, 0xa09b);

        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_SELECTOR, 0x10);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_LIMIT, 0xFFFFFFFFUL);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_ACCESS_RIGHTS, 0xa093);

        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_SELECTOR, 0x10);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_LIMIT, 0xFFFFFFFFUL);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_ACCESS_RIGHTS, 0xa093);

        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_SELECTOR, 0x10);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_LIMIT, 0xFFFFFFFFUL);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_ACCESS_RIGHTS, 0xa093);

        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_SELECTOR, 0x10);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_LIMIT, 0xFFFFFFFFUL);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_ACCESS_RIGHTS, 0xa093);

        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_SELECTOR, 0x10);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_LIMIT, 0xFFFFFFFFUL);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_ACCESS_RIGHTS, 0xa093);


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
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_HIGH, 0);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

            //guest MSR load on entry, store on exit
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_HIGH, 0);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_HIGH, 0);
            xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);

        }


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4) | CR4_PAE | CR4_PSE) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 9)) );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 15)) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE0_FULL, _guestslab1_init_pdpt[0] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE1_FULL, _guestslab1_init_pdpt[1] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE2_FULL, _guestslab1_init_pdpt[2] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE3_FULL, _guestslab1_init_pdpt[3] );


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, &_guestslab1_init_pml4t );
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, 0 );


        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR0, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0) & ~(CR0_PG) ) );
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_CR0_SHADOW, xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0));

        //TR, should be usable for VMX to work, but not used by guest
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_LIMIT, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_SELECTOR, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_TR_ACCESS_RIGHTS, 0x8B);

        //CS, DS, ES, FS, GS and SS segments
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_SELECTOR, 0x8);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_LIMIT, 0xFFFFFFFFUL);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CS_ACCESS_RIGHTS, 0xc09b);

        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_SELECTOR, 0x10);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_LIMIT, 0xFFFFFFFFUL);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_DS_ACCESS_RIGHTS, 0xc093);

        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_SELECTOR, 0x10);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_LIMIT, 0xFFFFFFFFUL);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_ES_ACCESS_RIGHTS, 0xc093);

        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_SELECTOR, 0x10);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_LIMIT, 0xFFFFFFFFUL);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_FS_ACCESS_RIGHTS, 0xc093);

        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_SELECTOR, 0x10);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_LIMIT, 0xFFFFFFFFUL);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GS_ACCESS_RIGHTS, 0xc093);

        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_SELECTOR, 0x10);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_BASE, 0);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_LIMIT, 0xFFFFFFFFUL);
        xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_SS_ACCESS_RIGHTS, 0xc093);



    }



















	/*_XDPRINTF_("%s: vmcs pinbased=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_PIN_BASED));
	_XDPRINTF_("%s: pinbase MSR=%016llx\n", __FUNCTION__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
	_XDPRINTF_("%s: cpu_based vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED));
	_XDPRINTF_("%s: cpu_based MSR=%016llx\n", __FUNCTION__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
	_XDPRINTF_("%s: seccpu_based vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED));
	_XDPRINTF_("%s: seccpu_based MSR=%016llx\n", __FUNCTION__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	_XDPRINTF_("%s: entrycontrols vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS));
	_XDPRINTF_("%s: entrycontrols MSR=%016llx\n", __FUNCTION__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);
	_XDPRINTF_("%s: exitcontrols vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_EXIT_CONTROLS));
	_XDPRINTF_("%s: exitcontrols MSR=%016llx\n", __FUNCTION__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
	_XDPRINTF_("%s: iobitmapa vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL));
	_XDPRINTF_("%s: iobitmapb vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap load vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap store vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap exit load vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL));
	_XDPRINTF_("%s: ept pointer vmcs=%016llx\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_EPT_POINTER_FULL));
    */
	_XDPRINTF_("%s: CR0 vmcs=%08x\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0));
	_XDPRINTF_("%s: CR4 vmcs=%08x\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4));
	_XDPRINTF_("%s: CR0 mask vmcs=%08x\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_CR0_MASK));
	_XDPRINTF_("%s: CR4 mask vmcs=%08x\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_CR4_MASK));
	_XDPRINTF_("%s: CR0 shadow vmcs=%08x\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_CR0_SHADOW));
	_XDPRINTF_("%s: CR4 shadow vmcs=%08x\n", __FUNCTION__, xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_CR4_SHADOW));


    return true;
}



void xmhf_hic_arch_setup_cpu_state(u64 cpuid){

	//replicate common MTRR state on this CPU
	#if !defined (__XMHF_VERIFICATION__)
	__xmhfhic_smp_cpu_x86_restorecpumtrrstate();
    #endif

    //load GDT
    __xmhfhic_x86vmx_loadGDT(&__xmhfhic_x86vmx_gdt);
    _XDPRINTF_("%s[%u]: GDT loaded\n", __FUNCTION__, (u32)cpuid);

    //load TR
    xmhfhw_cpu_loadTR( (__TRSEL + ((u32)cpuid * 16) ) );
    _XDPRINTF_("%s[%u]: TR loaded\n", __FUNCTION__, (u32)cpuid);

    //load IDT
    xmhfhw_cpu_loadIDT(&__xmhfhic_x86vmx_idt);
    _XDPRINTF_("%s[%u]: IDT loaded\n", __FUNCTION__, (u32)cpuid);

    ////turn on CR0.WP bit for supervisor mode write protection
    //write_cr0(read_cr0() | CR0_WP);
    //_XDPRINTF_("%s[%u]: Enabled supervisor mode write protection\n", __FUNCTION__, (u32)cpuid);

    //set IOPL3
    __xmhfhic_x86vmx_setIOPL3(cpuid);
    _XDPRINTF_("%s[%u]: set IOPL to CPL-3\n", __FUNCTION__, (u32)cpuid);


    //set LAPIC base address to preferred address
    {
        u64 msrapic = rdmsr64(MSR_APIC_BASE);
        wrmsr64(MSR_APIC_BASE, ((msrapic & 0x0000000000000FFFULL) | X86SMP_LAPIC_MEMORYADDRESS));
    }
    _XDPRINTF_("%s[%u]: set LAPIC base address to %016llx\n", __FUNCTION__, (u32)cpuid, rdmsr64(MSR_APIC_BASE));

	//turn on NX protections
    wrmsr64(MSR_EFER, (rdmsr64(MSR_EFER) | (1 << EFER_NXE)) );
    _XDPRINTF_("%s[%u]: NX protections enabled\n", __FUNCTION__, (u32)cpuid);


#if 0
	//enable PCIDE support
	{
		write_cr4(read_cr4() | CR4_PCIDE);
	}
    _XDPRINTF_("%s[%u]: PCIDE enabled\n", __FUNCTION__, (u32)cpuid);
#endif

	//set OSXSAVE bit in CR4 to enable us to pass-thru XSETBV intercepts
	//when the CPU supports XSAVE feature
	if(xmhf_baseplatform_arch_x86_cpuhasxsavefeature()){
        write_cr4(read_cr4() | CR4_OSXSAVE);
        _XDPRINTF_("%s[%u]: XSETBV passthrough enabled\n", __FUNCTION__, (u32)cpuid);
	}


	//set bit 5 (EM) of CR0 to be VMX compatible in case of Intel cores
	write_cr0(read_cr0() | 0x20);
    _XDPRINTF_("%s[%u]: Set CR0.EM to be VMX compatible\n", __FUNCTION__, (u32)cpuid);


    //setup SYSENTER/SYSEXIT mechanism
    {
        wrmsr(IA32_SYSENTER_CS_MSR, __CS_CPL0, 0);
        wrmsr(IA32_SYSENTER_EIP_MSR, (u32)&__xmhfhic_rtm_trampoline_stub, 0);
        wrmsr(IA32_SYSENTER_ESP_MSR, ((u32)__xmhfhic_rtm_trampoline_stack[(u32)cpuid] + MAX_PLATFORM_CPUSTACK_SIZE), 0);
    }
    _XDPRINTF_("%s: setup SYSENTER/SYSEXIT mechanism\n", __FUNCTION__);
    _XDPRINTF_("SYSENTER CS=%016llx\n", rdmsr64(IA32_SYSENTER_CS_MSR));
    _XDPRINTF_("SYSENTER RIP=%016llx\n", rdmsr64(IA32_SYSENTER_EIP_MSR));
    _XDPRINTF_("SYSENTER RSP=%016llx\n", rdmsr64(IA32_SYSENTER_ESP_MSR));


    //setup VMX state
    if(!__xmhfhic_x86vmx_setupvmxstate(cpuid)){
        _XDPRINTF_("%s[%u]: Unable to set VMX state. Halting!\n", __FUNCTION__, (u32)cpuid);
        HALT();
    }
    _XDPRINTF_("%s[%u]: Setup VMX state\n", __FUNCTION__, (u32)cpuid);

}


































#if 0

    //debug
    _XDPRINTF_("Halting!\n");
    _XDPRINTF_("XMHF Tester Finished!\n");
    HALT();

#endif // 0
