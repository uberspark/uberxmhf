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
#include <xc_init.h>




#if 1
u64 gp_uhslab_mempgtbl_getptflagsforspa_pae(u32 slabid, u32 spa, u32 spatype){
	u64 flags=0;
	u8 spa_slabtype, spa_slabregion;
	bool spa_sameslab=false;
	u32 slabtype = xmhfgeec_slab_info_table[slabid].slabtype;

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

        default:
            //_XDPRINTF_("%s: invalid slab type=%x. Halting!\n", __func__, slabtype);
            //HALT();
            flags = 0;
            break;

    }

    return flags;
}

#endif // 0









#if 1

void gp_s2_setupmpgtblu(void){
    slab_params_t spl;
    xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *initmempgtblp =
        (xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *)spl.in_out_params;
    u32 i, slabtype;

    _XDPRINTF_("%s: starting...\n", __func__);

    spl.src_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    spl.dst_slabid = XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL;
    spl.cpuid = 0; //XXX: fixme, need to plug in BSP cpuid here



    //setup verified slabs' page tables, uses slab index for GEEC_PRIME
    //spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL;
    //initmempgtblp->dst_slabid = XMHFGEEC_SLAB_GEEC_PRIME;
    //XMHF_SLAB_CALLNEW(&spl);
    //_geec_prime_populate_slab_pagetables_pae4k(XMHFGEEC_SLAB_GEEC_PRIME);

    //setup unverified slabs's page tables
    for(i=0; i < XMHFGEEC_TOTAL_SLABS; i++){
        slabtype = xmhfgeec_slab_info_table[i].slabtype;

        switch(slabtype){
            case XMHFGEEC_SLABTYPE_uVT_PROG:
            case XMHFGEEC_SLABTYPE_uVU_PROG:{
              	_XDPRINTF_("%s: slab %u --> ppopulating uV{T,U} page-tables...\n", __func__, i);
                gp_s2_setupmpgtbluh(i);
              	_XDPRINTF_("%s: slab %u --> uV{T,U}_prog page-tables populated\n", __func__, i);
            }
            break;


            case XMHFGEEC_SLABTYPE_uVT_PROG_GUEST:
            case XMHFGEEC_SLABTYPE_uVU_PROG_GUEST:
            case XMHFGEEC_SLABTYPE_uVU_PROG_RICHGUEST:{
              	_XDPRINTF_("%s: slab %u --> ppopulating uV{T,U}_prog_guest page-tables...\n", __func__, i);
                spl.dst_uapifn = XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL;
                initmempgtblp->dst_slabid = i;
                XMHF_SLAB_CALLNEW(&spl);
                gp_s2_setupmpgtblug(i);
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

#endif
