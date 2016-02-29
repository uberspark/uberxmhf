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

#include <geec_sentinel.h>
#include <xc.h>
#include <uapi_gcpustate.h>
//#include <uapi_slabmemacc.h>
#include <xg_benchguest.h>
#include <xc_testslab.h>
#include <xh_hyperdep.h>
#include <xh_syscalllog.h>
#include <xh_ssteptrace.h>
#include <xh_approvexec.h>

#include <xc_init.h>

//extern x_slab_info_t _xxmhfgeec_slab_info_table[XMHFGEEC_TOTAL_SLABS];


//////
//XMHF_SLABNEW(xcinit)

/*
 * slab code
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */


__attribute__(( aligned(16) )) static u64 _xcguestslab_init_gdt[]  = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00cf9b000000ffffULL,	//CPL-0 32-bit code descriptor (CS32)
	0x00cf93000000ffffULL,	//CPL-0 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x0000000000000000ULL,	//NULL descriptor
};



static u32 xc_hcbinvoke(u32 src_slabid, u32 cpuid, u32 cbtype, u32 cbqual, u32 guest_slab_index){
    u32 status = XC_HYPAPPCB_CHAIN;
    u32 i;
    slab_params_t spl;
    xc_hypappcb_params_t *hcbp = (xc_hypappcb_params_t *)&spl.in_out_params[0];

    spl.src_slabid = src_slabid;
    spl.cpuid = cpuid;
    spl.dst_uapifn = 0;
    hcbp->cbtype=cbtype;
    hcbp->cbqual=cbqual;
    hcbp->guest_slab_index=guest_slab_index;

    for(i=0; i < HYPAPP_INFO_TABLE_NUMENTRIES; i++){
        if(_xcihub_hypapp_info_table[i].cbmask & XC_HYPAPPCB_MASK(cbtype)){
            spl.dst_slabid = _xcihub_hypapp_info_table[i].xmhfhic_slab_index;
            XMHF_SLAB_CALLNEW(&spl);
            if(hcbp->cbresult == XC_HYPAPPCB_NOCHAIN){
                status = XC_HYPAPPCB_NOCHAIN;
                break;
            }
        }
    }

    return status;
}



void slab_main(slab_params_t *sp){

    //bool isbsp = (sp->cpuid & 0x80000000UL) ? true : false;
    bool isbsp = xmhfhw_lapic_isbsp();
    u64 inputval, outputval;
    //static u64 cpucount=0;
    static u32 __xcinit_smplock = 1;

    //_XDPRINTF_("XC_INIT[%u]: got control: ESP=%08x\n", __func__, (u16)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM));

    if(!isbsp){
        //_XDPRINTF_("XC_INIT[%u]: AP Halting!\n", __func__, (u16)sp->cpuid);

        //CASM_FUNCCALL(spin_lock,&__xcinit_smplock);
        //cpucount++;
        //CASM_FUNCCALL(spin_unlock,&__xcinit_smplock);

        HALT();
    }else{
        //BSP
        //_XDPRINTF_("%s[%u]: BSP waiting to rally APs...\n",
        //        __func__, (u16)sp->cpuid);

        //while(cpucount < (xcbootinfo->cpuinfo_numentries-1));

        //_XDPRINTF_("XC_INIT[%u]: BSP proceeding...\n",
        //        __func__, (u16)sp->cpuid);
    }

    _XDPRINTF_("XC_INIT[%u]: got control: ESP=%08x\n", (u16)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM));


    // call test slab
    {
        slab_params_t spl;
        spl.src_slabid = XMHFGEEC_SLAB_XC_INIT;
        spl.dst_slabid = XMHFGEEC_SLAB_XC_TESTSLAB;
        spl.cpuid = 0;
        spl.dst_uapifn = 0;
        spl.in_out_params[0] = 0xF00DDEAD;
        _XDPRINTF_("XC_INIT[%u]: proceeding to call test slab, esp=%x\n", (u16)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM));
        XMHF_SLAB_CALLNEW(&spl);
        _XDPRINTF_("XC_INIT[%u]: came back from test slab, esp=%x\n", (u16)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM));
        _XDPRINTF_("XC_INIT[%u]: called test slab, return value=%x\n",
                   (u16)sp->cpuid, spl.in_out_params[1]);
        //HALT();
    }



    {
        u32 guest_slab_header_paddr = xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XG_RICHGUEST].slab_physmem_extents[1].addr_start;
        u32 guest_slab_gdt_paddr = guest_slab_header_paddr + offsetof(guest_slab_header_t, gdt);
        u32 guest_slab_magic_paddr = guest_slab_header_paddr + offsetof(guest_slab_header_t, magic);
        u32 guest_slab_magic;


        //get and dump slab header magic
        {
            //slab_params_t spl;
            //xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)&spl.in_out_params[2];
            //xmhf_uapi_slabmemacc_params_t *smemaccp = (xmhf_uapi_slabmemacc_params_t *)spl.in_out_params;


            //smemaccp->dst_slabid = XMHFGEEC_SLAB_XG_RICHGUEST;
            //smemaccp->addr_to = &guest_slab_magic;
            //smemaccp->addr_from = guest_slab_magic_paddr;
            //smemaccp->numbytes = sizeof(guest_slab_magic);

            //spl.in_out_params[0] = XMHF_HIC_UAPI_PHYSMEM;
            //spl.dst_uapifn = XMHF_HIC_UAPI_PHYSMEM_PEEK;
            //spl.cpuid = sp->cpuid;
            //spl.src_slabid = XMHFGEEC_SLAB_XC_INIT;
            //spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMACC;

            //XMHF_SLAB_CALLNEW(&spl);
            CASM_FUNCCALL(xmhfhw_sysmemaccess_copy, &guest_slab_magic,
			guest_slab_magic_paddr, sizeof(guest_slab_magic));
            _XDPRINTF_("%s[%u]: guest slab header at=%x\n", __func__, (u16)sp->cpuid, guest_slab_header_paddr);
            _XDPRINTF_("%s[%u]: guest slab header magic=%x\n", __func__, (u16)sp->cpuid, guest_slab_magic);
        }


        //initialize guest slab gdt
        {
            //slab_params_t spl;
            //xmhf_hic_uapi_physmem_desc_t *pdesc = (xmhf_hic_uapi_physmem_desc_t *)&spl.in_out_params[2];
            //xmhf_uapi_slabmemacc_params_t *smemaccp = (xmhf_uapi_slabmemacc_params_t *)spl.in_out_params;

            /*smemaccp->dst_slabid = XMHFGEEC_SLAB_XG_RICHGUEST;
            smemaccp->addr_to = guest_slab_gdt_paddr;
            smemaccp->addr_from = &_xcguestslab_init_gdt;
            smemaccp->numbytes = sizeof(_xcguestslab_init_gdt);

            //spl.in_out_params[0] = XMHF_HIC_UAPI_PHYSMEM;
            spl.dst_uapifn = XMHF_HIC_UAPI_PHYSMEM_POKE;
            spl.cpuid = sp->cpuid;
            spl.src_slabid = XMHFGEEC_SLAB_XC_INIT;
            spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMACC;

            XMHF_SLAB_CALLNEW(&spl);*/
            CASM_FUNCCALL(xmhfhw_sysmemaccess_copy, guest_slab_gdt_paddr,
			&_xcguestslab_init_gdt, sizeof(_xcguestslab_init_gdt));
        }

        //setup guest slab VMCS GDT base and limit
        {
            slab_params_t spl;
            xmhf_uapi_gcpustate_vmrw_params_t *gcpustate_vmrwp =
                (xmhf_uapi_gcpustate_vmrw_params_t *)spl.in_out_params;

            spl.cpuid = sp->cpuid;
            spl.src_slabid = XMHFGEEC_SLAB_XC_INIT;
            spl.dst_slabid = XMHFGEEC_SLAB_UAPI_GCPUSTATE;

            //spl.in_out_params[0] = XMHF_HIC_UAPI_CPUSTATE;
            spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
            gcpustate_vmrwp->encoding = VMCS_GUEST_GDTR_BASE;
            gcpustate_vmrwp->value = guest_slab_gdt_paddr;

            XMHF_SLAB_CALLNEW(&spl);

            gcpustate_vmrwp->encoding = VMCS_GUEST_GDTR_LIMIT;
            gcpustate_vmrwp->value =  (sizeof(_xcguestslab_init_gdt)-1);

            XMHF_SLAB_CALLNEW(&spl);


		/*
		gcpustate_vmrwp->encoding = ;
		gcpustate_vmrwp->value = ;
		XMHF_SLAB_CALLNEW(&spl);
		*/

		//more guest-specific state setup
		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR4_SHADOW;
		gcpustate_vmrwp->value =(u64)CR4_VMXE;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_PAGEFAULT_ERRORCODE_MASK;
		gcpustate_vmrwp->value = 0x00000000;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_PAGEFAULT_ERRORCODE_MATCH;
		gcpustate_vmrwp->value = 0x00000000;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_EXCEPTION_BITMAP;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR3_TARGET_COUNT;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_VM_ENTRY_EXCEPTION_ERRORCODE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_CONTROL_VM_ENTRY_INTERRUPTION_INFORMATION;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_RSP;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_RIP;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_ACTIVITY_STATE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_RFLAGS;
		gcpustate_vmrwp->value = (1 <<1) | (EFLAGS_IOPL);
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_INTERRUPTIBILITY;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		//IDTR
		gcpustate_vmrwp->encoding = VMCS_GUEST_IDTR_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_IDTR_LIMIT;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		//LDTR, unusable
		gcpustate_vmrwp->encoding = VMCS_GUEST_LDTR_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_LDTR_LIMIT;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_LDTR_SELECTOR;
		gcpustate_vmrwp->value = 0 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_LDTR_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0x10000;
		XMHF_SLAB_CALLNEW(&spl);

		//guest CR3
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR3;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		//TR
		gcpustate_vmrwp->encoding = VMCS_GUEST_TR_BASE ;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_TR_LIMIT;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_TR_SELECTOR;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_TR_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0x8B;
		XMHF_SLAB_CALLNEW(&spl);

		//CS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_SELECTOR;
		gcpustate_vmrwp->value = 0x8;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_LIMIT;
		gcpustate_vmrwp->value = 0xFFFFFFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_CS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0xc09b;
		XMHF_SLAB_CALLNEW(&spl);

		//DS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_DS_SELECTOR;
		gcpustate_vmrwp->value = 0x10;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_DS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_DS_LIMIT;
		gcpustate_vmrwp->value = 0xFFFFFFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_DS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0xc093;
		XMHF_SLAB_CALLNEW(&spl);

		//ES segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_ES_SELECTOR;
		gcpustate_vmrwp->value = 0x10 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_ES_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_ES_LIMIT;
		gcpustate_vmrwp->value = 0xFFFFFFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_ES_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0xc093;
		XMHF_SLAB_CALLNEW(&spl);

		//FS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_FS_SELECTOR;
		gcpustate_vmrwp->value = 0x10 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_FS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_FS_LIMIT;
		gcpustate_vmrwp->value = 0xFFFFFFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_FS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0xc093;
		XMHF_SLAB_CALLNEW(&spl);

		//GS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_GS_SELECTOR;
		gcpustate_vmrwp->value = 0x10 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_GS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_GS_LIMIT;
		gcpustate_vmrwp->value = 0xFFFFFFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_GS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0xc093;
		XMHF_SLAB_CALLNEW(&spl);

		//SS segment
		gcpustate_vmrwp->encoding = VMCS_GUEST_SS_SELECTOR;
		gcpustate_vmrwp->value = 0x10 ;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_SS_BASE;
		gcpustate_vmrwp->value = 0;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_SS_LIMIT;
		gcpustate_vmrwp->value = 0xFFFFFFFFUL;
		XMHF_SLAB_CALLNEW(&spl);

		gcpustate_vmrwp->encoding = VMCS_GUEST_SS_ACCESS_RIGHTS;
		gcpustate_vmrwp->value = 0xc093;
		XMHF_SLAB_CALLNEW(&spl);


		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
		XMHF_SLAB_CALLNEW(&spl);
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
		gcpustate_vmrwp->value &= ~(CR0_PG);
		XMHF_SLAB_CALLNEW(&spl);

		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMREAD;
		gcpustate_vmrwp->encoding = VMCS_GUEST_CR0;
		XMHF_SLAB_CALLNEW(&spl);
		spl.dst_uapifn = XMHF_HIC_UAPI_CPUSTATE_VMWRITE;
		gcpustate_vmrwp->encoding = VMCS_CONTROL_CR0_SHADOW;
		XMHF_SLAB_CALLNEW(&spl);

	}

    }


/*    //debug
    _XDPRINTF_("Halting!\n");
    _XDPRINTF_("XMHF Tester Finished!\n");
    HALT();
*/

    //invoke hypapp initialization callbacks
    xc_hcbinvoke(XMHFGEEC_SLAB_XC_INIT,
                 sp->cpuid, XC_HYPAPPCB_INITIALIZE, 0, XMHFGEEC_SLAB_XG_RICHGUEST);


    //call guestslab
    {
        slab_params_t spl;

        memset(&spl, 0, sizeof(spl));
        spl.cpuid = sp->cpuid;
        spl.src_slabid = XMHFGEEC_SLAB_XC_INIT;
        spl.dst_slabid = XMHFGEEC_SLAB_XG_RICHGUEST;

        _XDPRINTF_("%s[%u]: Proceeding to call xcguestslab; ESP=%08x, eflags=%08x\n", __func__, (u16)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM),
			CASM_FUNCCALL(read_eflags, CASM_NOPARAM));

        XMHF_SLAB_CALLNEW(&spl);
    }


    _XDPRINTF_("%s[%u]: Should  never get here.Halting!\n", __func__, (u16)sp->cpuid);
    HALT();

    return;
}








#if 0


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

	_XDPRINTF_("%s: CR0 vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR0));
	_XDPRINTF_("%s: CR4 vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR4));
	_XDPRINTF_("%s: CR0 mask vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR0_MASK));
	_XDPRINTF_("%s: CR4 mask vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR4_MASK));
	_XDPRINTF_("%s: CR0 shadow vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR0_SHADOW));
	_XDPRINTF_("%s: CR4 shadow vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR4_SHADOW));
	*/


	//MSR bitmap support
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_MSR_BITMAPS_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msrbitmaps_region );
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 28)) );

	//setup NMI intercept for core-quiescing
	//XXX: needs to go in xcinit/richguest slab
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_PIN_BASED) | (u64)(1 << 3) ) );


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4) | CR4_PAE | CR4_PSE) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 9)) );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 15)) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE0_FULL, _guestslab1_init_pdpt[0] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE1_FULL, _guestslab1_init_pdpt[1] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE2_FULL, _guestslab1_init_pdpt[2] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE3_FULL, _guestslab1_init_pdpt[3] );


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, &_guestslab1_init_pml4t );



    /*
    x86_64
    //64-bit host
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_CONTROLS, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_EXIT_CONTROLS) | (1 << 9)) );
    */

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
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, (void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

            //guest MSR load on entry, store on exit
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, (void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, (void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
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



    _xcinit_dotests(cpuid);

    _XDPRINTF_("%s[%u]: Should  never get here.Halting!\n",
        __func__, (u32)cpuid);

    HALT();


#endif // 0
