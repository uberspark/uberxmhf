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
 * slab memory pagetable uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <xc.h>
#include <geec_sentinel.h>
#include <uapi_slabmempgtbl.h>


//////
// backing data buffers for slab memory and device page tables
#if !defined (__XMHF_VERIFICATION__)

__attribute__((section(".data"))) __attribute__(( aligned(2097152) )) u64 _dbuf_mempgtbl_pml4t[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PML4T];
__attribute__((section(".data"))) __attribute__((aligned(4096)))	u64 _dbuf_mempgtbl_pdpt[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PDPT];
__attribute__((section(".data"))) __attribute__((aligned(4096)))	u64 _dbuf_mempgtbl_pdt[XMHF_HIC_MAX_SLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
__attribute__((section(".data"))) __attribute__((aligned(4096)))  u64 _dbuf_mempgtbl_pt[XMHF_HIC_MAX_SLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT][PAE_PTRS_PER_PT];

#endif //__XMHF_VERIFICATION__


__attribute__((section(".rwdatahdr"))) __attribute__((aligned(4096))) u64 _slabmempgtbl_lvl4t[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PML4T];
__attribute__((section(".data"))) __attribute__((aligned(4096))) u64 _slabmempgtbl_lvl3t[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PDPT];
__attribute__((section(".data"))) __attribute__((aligned(4096))) u64 _slabmempgtbl_lvl2t[XMHF_HIC_MAX_SLABS][PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
__attribute__((section(".data"))) __attribute__((aligned(4096)))  u64 _slabmempgtbl_lvl1t_mmio[XMHF_HIC_MAX_SLABS][PAE_PTRS_PER_PT];
__attribute__((section(".data"))) __attribute__((aligned(4096)))  u64 _slabmempgtbl_lvl1t_richguest[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT][PAE_PTRS_PER_PT];


static void _slabmempgtbl_initmempgtbl_pae2Mmmio(u32 slabid){
    //pdpt = _slabmempgtbl_lvl4t[slabid];
    //pdt = _slabmempgtbl_lvl2t[slabid];
    //mmio = _slabmempgtbl_lvl1t_mmio[slabid];
    u32 i;
    u64 default_flags = (u64)(_PAGE_PRESENT);
    u32 mmio_paddr;
    u32 pdpt_index, pdt_index;

    //setup pdpt to point to pdts
    memset(&_slabmempgtbl_lvl4t[slabid], 0, PAGE_SIZE_4K);
    for(i=0; i < PAE_PTRS_PER_PDPT; i++){
        _slabmempgtbl_lvl4t[slabid][i] =
            pae_make_pdpe(&_slabmempgtbl_lvl2t[slabid][i], default_flags);
    }

    //splinter mmio page into 4K mappings
    mmio_paddr = _xmhfhic_common_slab_info_table[slabid].slab_physmem_extents[4].addr_start;
    pdpt_index = pae_get_pdpt_index(mmio_paddr);
    pdt_index = pae_get_pdt_index(mmio_paddr);
    _slabmempgtbl_lvl2t[slabid][pdpt_index][pdt_index] =
        pae_make_pde(&_slabmempgtbl_lvl1t_mmio[slabid], default_flags);

}

static void _slabmempgtbl_initmempgtbl_ept4K(u32 slabid){
    //pml4t = _slabmempgtbl_lvl4t[slabid];
    //pdpt = _slabmempgtbl_lvl3t[slabid];
    //pdt = _slabmempgtbl_lvl2t[slabid];
    //pt = _slabmempgtbl_lvl1t_richguest[slabid];
    u32 i, j;

    //pml4t
    memset(&_slabmempgtbl_lvl4t[slabid], 0, PAGE_SIZE_4K);
    for(i=0; i < PAE_PTRS_PER_PML4T; i++)
        _slabmempgtbl_lvl4t[slabid][i] =
            ((u64)&_slabmempgtbl_lvl3t[slabid] | 0x7);

    //pdpt
    memset(&_slabmempgtbl_lvl3t[slabid], 0, PAGE_SIZE_4K);
    for(i=0; i < PAE_PTRS_PER_PDPT; i++)
		_slabmempgtbl_lvl3t[slabid][i] =
            ((u64)&_slabmempgtbl_lvl2t[slabid][i] | 0x7 );

    //pdt
	for(i=0; i < PAE_PTRS_PER_PDPT; i++){
		for(j=0; j < PAE_PTRS_PER_PDT; j++){
			_slabmempgtbl_lvl2t[slabid][i][j] =
                ((u64)&_slabmempgtbl_lvl1t_richguest[i][j] | 0x7 );
		}
	}
}


static void _slabmempgtbl_initmempgtbl_ept2Mmmio(u32 slabid){
    //pml4t = _slabmempgtbl_lvl4t[slabid];
    //pdpt = _slabmempgtbl_lvl3t[slabid];
    //pdt = _slabmempgtbl_lvl2t[slabid];
    //mmio = _slabmempgtbl_lvl1t_mmio[slabid];
    u32 i, j;
    u32 mmio_paddr;
    u32 pdpt_index, pdt_index;

    //pml4t
    memset(&_slabmempgtbl_lvl4t[slabid], 0, PAGE_SIZE_4K);
    for(i=0; i < PAE_PTRS_PER_PML4T; i++)
        _slabmempgtbl_lvl4t[slabid][i] =
            ((u64)&_slabmempgtbl_lvl3t[slabid] | 0x7);

    //pdpt
    memset(&_slabmempgtbl_lvl3t[slabid], 0, PAGE_SIZE_4K);
    for(i=0; i < PAE_PTRS_PER_PDPT; i++)
		_slabmempgtbl_lvl3t[slabid][i] =
            ((u64)&_slabmempgtbl_lvl2t[slabid][i] | 0x7 );

    //pdt
    memset(&_slabmempgtbl_lvl2t[slabid], 0, PAE_PTRS_PER_PDPT * PAGE_SIZE_4K);
    //splinter mmio page into 4K mappings
    mmio_paddr = _xmhfhic_common_slab_info_table[slabid].slab_physmem_extents[4].addr_start;
    pdpt_index = pae_get_pdpt_index(mmio_paddr);
    pdt_index = pae_get_pdt_index(mmio_paddr);
    _slabmempgtbl_lvl2t[slabid][pdpt_index][pdt_index] =
        ((u64)&_slabmempgtbl_lvl1t_mmio[slabid] | 0x7 );

}


static void _slabmempgtbl_initmempgtbl(u32 slabid){
    u32 slabtype;

    //sanity checks
    if(slabid >= XMHF_HIC_MAX_SLABS)
        return;

    slabtype = _xmhfhic_common_slab_info_table[slabid].archdata.slabtype;

    switch(slabtype){
        case XMHFGEEC_SLABTYPE_TPROGSLAB:
        case XMHFGEEC_SLABTYPE_UPROGSLAB:
        case XMHFGEEC_SLABTYPE_TPRIMESLAB:{
            _slabmempgtbl_initmempgtbl_pae2Mmmio(slabid);
            _XDPRINTF_("%s: setup slab %u with pae2Mmmio\n", __func__, slabid);
        }
        break;

        case XMHFGEEC_SLABTYPE_UGPROGSLAB:{
            _slabmempgtbl_initmempgtbl_ept2Mmmio(slabid);
            _XDPRINTF_("%s: setup slab %u with ept2Mmmio\n", __func__, slabid);
        }
        break;

        case XMHFGEEC_SLABTYPE_UGRICHGUESTSLAB:{
            _slabmempgtbl_initmempgtbl_ept4K(slabid);
            _XDPRINTF_("%s: setup slab %u with ept4K\n", __func__, slabid);
        }
        break;

        default:
            _XDPRINTF_("%s: unknown slab type %u\n", __func__, slabtype);
            break;
    }

}


static void _slabmempgtbl_setentryforpaddr(u32 slabid, u64 gpa, u64 entry){

    u64 pdpt_index = pae_get_pdpt_index(gpa);
    u64 pdt_index = pae_get_pdt_index(gpa);
    u64 pt_index = pae_get_pt_index(gpa);
    u32 slabtype, mmio_paddr;

    //sanity checks
    if(slabid >= XMHF_HIC_MAX_SLABS)
        return;

    slabtype = _xmhfhic_common_slab_info_table[slabid].archdata.slabtype;
    mmio_paddr = _xmhfhic_common_slab_info_table[slabid].slab_physmem_extents[4].addr_start;

    switch(slabtype){

        case XMHFGEEC_SLABTYPE_TPROGSLAB:
        case XMHFGEEC_SLABTYPE_UPROGSLAB:
        case XMHFGEEC_SLABTYPE_TPRIMESLAB:
        case XMHFGEEC_SLABTYPE_UGPROGSLAB:{
            //2M mappings with 4K splintered mmio
            if(gpa >= mmio_paddr && gpa < (mmio_paddr + PAGE_SIZE_2M)){
                _slabmempgtbl_lvl1t_mmio[slabid][pt_index] = entry;
            }else{
                _slabmempgtbl_lvl2t[slabid][pdpt_index][pdt_index] = entry;
            }
        }
        break;

        case XMHFGEEC_SLABTYPE_UGRICHGUESTSLAB:{
            //4K mappings throughout
            _slabmempgtbl_lvl1t_richguest[pdpt_index][pdt_index][pt_index] =
                entry;
        }
        break;

        default:
            _XDPRINTF_("%s: unknown slab type %u\n", __func__, slabtype);
            break;

    }

}


static u64 _slabmempgtbl_getentryforpaddr(u32 slabid, u64 gpa){
    u64 result_entry=0;
    u64 pdpt_index = pae_get_pdpt_index(gpa);
    u64 pdt_index = pae_get_pdt_index(gpa);
    u64 pt_index = pae_get_pt_index(gpa);
    u32 slabtype, mmio_paddr;

    //sanity checks
    if(slabid >= XMHF_HIC_MAX_SLABS)
        return;

    slabtype = _xmhfhic_common_slab_info_table[slabid].archdata.slabtype;
    mmio_paddr = _xmhfhic_common_slab_info_table[slabid].slab_physmem_extents[4].addr_start;

    switch(slabtype){

        case XMHFGEEC_SLABTYPE_TPROGSLAB:
        case XMHFGEEC_SLABTYPE_UPROGSLAB:
        case XMHFGEEC_SLABTYPE_TPRIMESLAB:
        case XMHFGEEC_SLABTYPE_UGPROGSLAB:{
            //2M mappings with 4K splintered mmio
            if(gpa >= mmio_paddr && gpa < (mmio_paddr + PAGE_SIZE_2M)){
                result_entry = _slabmempgtbl_lvl1t_mmio[slabid][pt_index];
            }else{
                result_entry = _slabmempgtbl_lvl2t[slabid][pdpt_index][pdt_index];
            }
        }
        break;

        case XMHFGEEC_SLABTYPE_UGRICHGUESTSLAB:{
            //4K mappings throughout
            result_entry = _slabmempgtbl_lvl1t_richguest[pdpt_index][pdt_index][pt_index];
        }
        break;

        default:
            _XDPRINTF_("%s: unknown slab type %u\n", __func__, slabtype);
            break;

    }

    return result_entry;
}


/////
void slab_main(slab_params_t *sp){

    xmhf_uapi_params_hdr_t *uapiphdr = (xmhf_uapi_params_hdr_t *)sp->in_out_params;

    switch(uapiphdr->uapifn){

       case XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL:{
            xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *initmempgtblp =
                (xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *)sp->in_out_params;

            _slabmempgtbl_initmempgtbl(initmempgtblp->dst_slabid);
       }
       break;


       case XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR:{
            xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp =
                (xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *)sp->in_out_params;

            _slabmempgtbl_setentryforpaddr(setentryforpaddrp->dst_slabid,
                                           setentryforpaddrp->gpa,
                                           setentryforpaddrp->entry);

       }
        break;

       case XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR:{
            xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp =
                (xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *)sp->in_out_params;

            getentryforpaddrp->result_entry = _slabmempgtbl_getentryforpaddr(getentryforpaddrp->dst_slabid,
                                           getentryforpaddrp->gpa);

       }
        break;


       case XMHF_HIC_UAPI_MEMPGTBL_GETENTRY:{
            xmhf_uapi_slabmempgtbl_entry_params_t *smempgtblentryp =
                (xmhf_uapi_slabmempgtbl_entry_params_t *)sp->in_out_params;

            {
                u64 pdpt_index = pae_get_pdpt_index(smempgtblentryp->gpa);
                u64 pd_index = pae_get_pdt_index(smempgtblentryp->gpa);
                u64 pt_index = pae_get_pt_index(smempgtblentryp->gpa);
                smempgtblentryp->entry =
                    _dbuf_mempgtbl_pt[smempgtblentryp->dst_slabid][pdpt_index][pd_index][pt_index];
            }

        }
        break;


        case XMHF_HIC_UAPI_MEMPGTBL_SETENTRY:{
            xmhf_uapi_slabmempgtbl_entry_params_t *smempgtblentryp =
                (xmhf_uapi_slabmempgtbl_entry_params_t *)sp->in_out_params;

            {
                u64 pdpt_index = pae_get_pdpt_index(smempgtblentryp->gpa);
                u64 pd_index = pae_get_pdt_index(smempgtblentryp->gpa);
                u64 pt_index = pae_get_pt_index(smempgtblentryp->gpa);
                _dbuf_mempgtbl_pt[smempgtblentryp->dst_slabid][pdpt_index][pd_index][pt_index]
                    = smempgtblentryp->entry;

            }

        }
        break;



        default:
            _XDPRINTF_("UAPI_SLABMEMPGTBL[%u]: Unknown uAPI function %x. Halting!\n",
                    (u16)sp->cpuid, uapiphdr->uapifn);
            HALT();
            return;
    }


}
