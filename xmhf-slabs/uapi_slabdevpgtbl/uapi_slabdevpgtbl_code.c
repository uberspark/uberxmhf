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
 * slab device pagetable uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <geec_sentinel.h>
#include <uapi_slabdevpgtbl.h>


__attribute__((section(".data"))) __attribute__((aligned(4096))) static vtd_ret_entry_t _slabdevpgtbl_vtd_ret[VTD_RET_MAXPTRS];
__attribute__((section(".data"))) __attribute__((aligned(4096))) static vtd_cet_entry_t _slabdevpgtbl_vtd_cet[VTD_RET_MAXPTRS][VTD_CET_MAXPTRS];

__attribute__((section(".data"))) static bool _slabdevpgtbl_init_done = false;
__attribute__((section(".data"))) static bool _slabdevpgtbl_initretcet_done = false;




__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pml4te_t _slabdevpgtbl_pml4t[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PML4T];
__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pdpte_t _slabdevpgtbl_pdpt[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PDPT];
__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pdte_t _slabdevpgtbl_pdt[XMHF_HIC_MAX_SLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
__attribute__((section(".data"))) __attribute__((aligned(4096))) vtd_pte_t _slabdevpgtbl_pt[XMHF_HIC_MAX_SLABS][16][PAE_PTRS_PER_PT];
__attribute__((section(".data"))) _slabdevpgtbl_infotable_t _slabdevpgtbl_infotable[XMHF_HIC_MAX_SLABS];


static void _slabdevpgtbl_init(void){
    u32 i;

    for(i=0; i < XMHF_HIC_MAX_SLABS; i++){
        _slabdevpgtbl_infotable[i].paddr_lvl1table = 0;
        _slabdevpgtbl_infotable[i].paddr_lvl2table = 0;
        _slabdevpgtbl_infotable[i].devpgtbl_initialized=false;
    }

}



static void _slabdevpgtbl_initretcet(void){
    u32 i, j;

    for(i=0; i< VTD_RET_MAXPTRS; i++){
        _slabdevpgtbl_vtd_ret[i].qwords[0] =
            vtd_make_rete((u64)&_slabdevpgtbl_vtd_cet[i], VTD_RET_PRESENT);
        _slabdevpgtbl_vtd_ret[i].qwords[1] = 0ULL;

        for(j=0; j < VTD_CET_MAXPTRS; j++){
            _slabdevpgtbl_vtd_cet[i][j].qwords[0] =
                _slabdevpgtbl_vtd_cet[i][j].qwords[1] = 0ULL;
        }
    }
}



static void _slabdevpgtbl_initdevpgtbl(u32 slabid){
    u32 i;
    u64 default_flags = (VTD_PAGE_READ | VTD_PAGE_WRITE);
    u32 paddr=0, pt_paddr;
    u32 pt_index=0;
    u32 paddr_dmadata_start, paddr_dmadata_end;

    paddr_dmadata_start =
        _xmhfhic_common_slab_info_table[slabid].slab_physmem_extents[3].addr_start;
    paddr_dmadata_end =
        _xmhfhic_common_slab_info_table[slabid].slab_physmem_extents[3].addr_end;

    //sanity checks
    if(slabid > XMHF_HIC_MAX_SLABS){
        _XDPRINTF_("%s: Error: slabid (%u) > XMHF_HIC_MAX_SLABS(%u). bailing out!\n", __func__, slabid, XMHF_HIC_MAX_SLABS);
        return;
    }
    if( (paddr_dmadata_end - paddr_dmadata_start) >
        (PAGE_SIZE_2M * 16) ){
        _XDPRINTF_("%s: Error: slab %u dmadata section over limit. bailing out!\n",
                   __func__, slabid);
        return;
    }


    //initialize lvl1 page table (pml4t)
    memset(&_slabdevpgtbl_pml4t[slabid], 0, sizeof(_slabdevpgtbl_pml4t[0]));
    _slabdevpgtbl_pml4t[slabid][0] =
        vtd_make_pml4te((u64)_slabdevpgtbl_pdpt[slabid], default_flags);

    //initialize lvl2 page table (pdpt)
    memset(&_slabdevpgtbl_pdpt[slabid], 0, sizeof(_slabdevpgtbl_pdpt[0]));
    for(i=0; i < VTD_PTRS_PER_PDPT; i++){
        _slabdevpgtbl_pdpt[slabid][i] =
            vtd_make_pdpte((u64)_slabdevpgtbl_pdt[slabid][i], default_flags);
    }


    paddr = paddr_dmadata_start;

    do {
        //grab index of pdpt, pdt this paddr
        u32 pdpt_index = pae_get_pdpt_index(paddr);
        u32 pdt_index = pae_get_pdt_index(paddr);

        //stick a pt for the pdt entry
        _slabdevpgtbl_pdt[slabid][pdpt_index][pdt_index] =
            vtd_make_pdte((u64)_slabdevpgtbl_pt[slabid][pt_index], default_flags);

        //populate pt entries
        pt_paddr = paddr;
        for(i=0; i < VTD_PTRS_PER_PT; i++){
            _slabdevpgtbl_pt[slabid][pt_index][i] =
                vtd_make_pte(pt_paddr, default_flags);
            pt_paddr += PAGE_SIZE_4K;
        }

        pt_index++;
        paddr += PAGE_SIZE_2M;
    } while (paddr < paddr_dmadata_end);


    _slabdevpgtbl_infotable[slabid].paddr_lvl1table = (u32)&_slabdevpgtbl_pml4t[slabid];
    _slabdevpgtbl_infotable[slabid].paddr_lvl2table = (u32)&_slabdevpgtbl_pdpt[slabid];
    _slabdevpgtbl_infotable[slabid].devpgtbl_initialized = true;

}



/////
void slab_main(slab_params_t *sp){

    xmhf_uapi_params_hdr_t *uapiphdr = (xmhf_uapi_params_hdr_t *)sp->in_out_params;

    switch(uapiphdr->uapifn){
        case XMHFGEEC_UAPI_SDEVPGTBL_INIT:{
            if(!_slabdevpgtbl_init_done){
                _slabdevpgtbl_init();
                _slabdevpgtbl_init_done=true;
            }
        }
        break;


        case XMHFGEEC_UAPI_SDEVPGTBL_INITRETCET:{
            xmhfgeec_uapi_slabdevpgtbl_initretcet_params_t *initretcetp =
                (xmhfgeec_uapi_slabdevpgtbl_initretcet_params_t *)sp->in_out_params;

            if(_slabdevpgtbl_init_done){
                if(!_slabdevpgtbl_initretcet_done){
                    _slabdevpgtbl_initretcet();
                    _slabdevpgtbl_initretcet_done = true;
                }

                initretcetp->result_retpaddr = (u32)&_slabdevpgtbl_vtd_ret;
            }else{
                initretcetp->result_retpaddr = 0;
            }

        }
        break;


        case XMHFGEEC_UAPI_SDEVPGTBL_INITDEVPGTBL:{
            xmhfgeec_uapi_slabdevpgtbl_initdevpgtbl_params_t *initdevpgtbl =
                (xmhfgeec_uapi_slabdevpgtbl_initdevpgtbl_params_t *)sp->in_out_params;

            if(_slabdevpgtbl_init_done)
                _slabdevpgtbl_initdevpgtbl(initdevpgtbl->dst_slabid);
        }
        break;


        default:
            _XDPRINTF_("UAPI_SLABDEVPGTBL[%u]: Unknown uAPI function %x. Halting!\n",
                    (u16)sp->cpuid, uapiphdr->uapifn);
            HALT();
            return;
    }


}
