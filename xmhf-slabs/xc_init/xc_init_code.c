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
#include <xg_richguest.h>
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

	_XDPRINTF_("%s[%u]: Got control: ESP=%08x\n", __func__, (u16)sp->cpuid, CASM_FUNCCALL(read_esp,CASM_NOPARAM));

    if(!isbsp){
        _XDPRINTF_("%s[%u]: AP Halting!\n", __func__, (u16)sp->cpuid);

        //CASM_FUNCCALL(spin_lock,&__xcinit_smplock);
        //cpucount++;
        //CASM_FUNCCALL(spin_unlock,&__xcinit_smplock);

        HALT();
    }else{
        //BSP
        //_XDPRINTF_("%s[%u]: BSP waiting to rally APs...\n",
        //        __func__, (u16)sp->cpuid);

        //while(cpucount < (xcbootinfo->cpuinfo_numentries-1));

        _XDPRINTF_("%s[%u]: BSP, APs halted. Proceeding...\n",
                __func__, (u16)sp->cpuid);
    }



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


    _xcinit_dotests(cpuid);

    _XDPRINTF_("%s[%u]: Should  never get here.Halting!\n",
        __func__, (u32)cpuid);

    HALT();


#endif // 0
