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
#include <xc_init.h>




void gp_s1_bspstack(slab_params_t *sp){
	u32 paddr=0;
	u32 i, j;
	u64 pdpe_flags = (_PAGE_PRESENT);
	u64 pdte_flags = (_PAGE_RW | _PAGE_PSE | _PAGE_PRESENT);





    memset(&_xcprimeon_init_pdpt, 0, sizeof(_xcprimeon_init_pdpt));

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


    {
	u64 msr_efer;
	msr_efer = (CASM_FUNCCALL(rdmsr64, MSR_EFER) | (0x800));
	CASM_FUNCCALL(wrmsr64,MSR_EFER, (u32)msr_efer, (u32)((u64)msr_efer >> 32) );
        _XDPRINTF_("EFER=%016llx\n", CASM_FUNCCALL(rdmsr64,MSR_EFER));
	CASM_FUNCCALL(write_cr4,read_cr4(CASM_NOPARAM) | (0x30) );
        _XDPRINTF_("CR4=%08x\n", CASM_FUNCCALL(read_cr4,CASM_NOPARAM));
	CASM_FUNCCALL(write_cr3,(u32)&_xcprimeon_init_pdpt);
        _XDPRINTF_("CR3=%08x\n", CASM_FUNCCALL(read_cr3,CASM_NOPARAM));
	CASM_FUNCCALL(write_cr0,0x80000015);
    }


	gp_s1_hub();
}

