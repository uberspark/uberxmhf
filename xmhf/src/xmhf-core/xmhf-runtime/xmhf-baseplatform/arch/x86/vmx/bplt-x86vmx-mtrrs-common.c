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
 * XMHF: The following file is taken from:
 *  tboot-1.10.5/tboot/txt/mtrrs.c
 * Changes made include:
 *  Split to bplt-x86vmx-mtrrs-common.c and bplt-x86vmx-mtrrs-bootloader.c .
 *  Remove use of global variable g_saved_mtrrs.
 *  Remove call to validate_mmio_regions() in validate_mtrrs()
 * The list of symbols in the order of appearance in mtrrs.c is:
 *  symbol                  location    comment
 *  MTRR_TYPE_MIXED         common
 *  MMIO_APIC_BASE          common
 *  NR_MMIO_APIC_PAGES      common
 *  NR_MMIO_IOAPIC_PAGES    common
 *  NR_MMIO_PCICFG_PAGES    common
 *  SINIT_MTRR_MASK         bootloader
 *  g_saved_mtrrs           discarded
 *  get_maxphyaddr_mask     common
 *  set_mtrrs_for_acmod     bootloader
 *  save_mtrrs              bootloader
 *  print_mtrrs             common      set to non-static
 *  get_page_type           discarded
 *  get_region_type         discarded
 *  validate_mmio_regions   discarded
 *  validate_mtrrs          common
 *  restore_mtrrs           common
 *  set_mem_type            bootloader
 *  set_all_mtrrs           common
 */

/*
 * mtrrs.c: support functions for manipulating MTRRs
 *
 * Copyright (c) 2003-2010, Intel Corporation
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above
 *     copyright notice, this list of conditions and the following
 *     disclaimer in the documentation and/or other materials provided
 *     with the distribution.
 *   * Neither the name of the Intel Corporation nor the names of its
 *     contributors may be used to endorse or promote products derived
 *     from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#include <xmhf.h>

#define MTRR_TYPE_MIXED         -1
#define MMIO_APIC_BASE          0xFEE00000
#define NR_MMIO_APIC_PAGES      1
#define NR_MMIO_IOAPIC_PAGES    1
#define NR_MMIO_PCICFG_PAGES    1

static uint64_t get_maxphyaddr_mask(void)
{
    static bool printed_msg = false;
    union {
        uint32_t raw;
        struct {
	    uint32_t num_pa_bits  : 8;
	    uint32_t num_la_bits  : 8;
	    uint32_t reserved     : 16;
	};
    } num_addr_bits;

    /* does CPU support 0x80000008 CPUID leaf? (all TXT CPUs should) */
    uint32_t max_ext_fn = cpuid_eax(0x80000000);
    if ( max_ext_fn < 0x80000008 )
        return 0xffffff;      /* if not, default is 36b support */

    num_addr_bits.raw = cpuid_eax(0x80000008);
    if ( !printed_msg ) {
        printf("CPU supports %u phys address bits\n", num_addr_bits.num_pa_bits);
	printed_msg = true;
    }
    return ((1ULL << num_addr_bits.num_pa_bits) - 1) >> PAGE_SHIFT_4K;
}

void print_mtrrs(const mtrr_state_t *saved_state)
{
    printf("mtrr_def_type: e = %d, fe = %d, type = %x\n",
           saved_state->mtrr_def_type.e, saved_state->mtrr_def_type.fe,
           saved_state->mtrr_def_type.type );
    printf("mtrrs:\n");
    printf("\t\t    base          mask      type  v\n");
    for ( unsigned int i = 0; i < saved_state->num_var_mtrrs; i++ ) {
        printf("\t\t%13.13llx %13.13llx  %2.2x  %d\n",
               (uint64_t)saved_state->mtrr_physbases[i].base,
               (uint64_t)saved_state->mtrr_physmasks[i].mask,
               saved_state->mtrr_physbases[i].type,
               saved_state->mtrr_physmasks[i].v );
    }
}

bool validate_mtrrs(const mtrr_state_t *saved_state)
{
    mtrr_cap_t mtrr_cap;
    uint64_t maxphyaddr_mask = get_maxphyaddr_mask();
    uint64_t max_pages = maxphyaddr_mask + 1;  /* max # 4k pages supported */

    /* check is meaningless if MTRRs were disabled */
    if ( saved_state->mtrr_def_type.e == 0 )
        return true;

    /* number variable MTRRs */
    mtrr_cap.raw = rdmsr64(MSR_MTRRcap);
    if ( mtrr_cap.vcnt < saved_state->num_var_mtrrs ) {
        printf("actual # var MTRRs (%d) < saved # (%d)\n",
               mtrr_cap.vcnt, saved_state->num_var_mtrrs);
        return false;
    }

    /* variable MTRRs describing non-contiguous memory regions */
    for ( unsigned int ndx = 0; ndx < saved_state->num_var_mtrrs; ndx++ ) {
        uint64_t tb;

        if ( saved_state->mtrr_physmasks[ndx].v == 0 )
            continue;

        for ( tb = 1; tb != max_pages; tb = tb << 1 ) {
            if ( (tb & saved_state->mtrr_physmasks[ndx].mask & maxphyaddr_mask)
                 != 0 )
                break;
        }
        for ( ; tb != max_pages; tb = tb << 1 ) {
            if ( (tb & saved_state->mtrr_physmasks[ndx].mask & maxphyaddr_mask)
                 == 0 )
                break;
        }
        if ( tb != max_pages ) {
	    printf("var MTRRs with non-contiguous regions: base=0x%llx, mask=0x%llx\n",
                   (uint64_t)saved_state->mtrr_physbases[ndx].base
                                  & maxphyaddr_mask,
                   (uint64_t)saved_state->mtrr_physmasks[ndx].mask
                                  & maxphyaddr_mask);
            print_mtrrs(saved_state);
            return false;
        }
    }

    /* overlaping regions with invalid memory type combinations */
    for ( unsigned int ndx = 0; ndx < saved_state->num_var_mtrrs; ndx++ ) {
        const mtrr_physbase_t *base_ndx = &saved_state->mtrr_physbases[ndx];
        const mtrr_physmask_t *mask_ndx = &saved_state->mtrr_physmasks[ndx];

        if ( mask_ndx->v == 0 )
            continue;

        for ( unsigned int i = ndx + 1; i < saved_state->num_var_mtrrs; i++ ) {
            const mtrr_physbase_t *base_i = &saved_state->mtrr_physbases[i];
            const mtrr_physmask_t *mask_i = &saved_state->mtrr_physmasks[i];
            unsigned int j;

            if ( mask_i->v == 0 )
                continue;

            if ( (base_ndx->base & mask_ndx->mask & mask_i->mask & maxphyaddr_mask)
                    != (base_i->base & mask_i->mask & maxphyaddr_mask) &&
                 (base_i->base & mask_i->mask & mask_ndx->mask & maxphyaddr_mask)
                    != (base_ndx->base & mask_ndx->mask & maxphyaddr_mask) )
                continue;

            if ( base_ndx->type == base_i->type )
                continue;
            if ( base_ndx->type == MTRR_TYPE_UNCACHABLE
                 || base_i->type == MTRR_TYPE_UNCACHABLE )
                continue;
            if ( base_ndx->type == MTRR_TYPE_WRTHROUGH
                 && base_i->type == MTRR_TYPE_WRBACK )
                continue;
            if ( base_ndx->type == MTRR_TYPE_WRBACK
                 && base_i->type == MTRR_TYPE_WRTHROUGH )
                continue;

            /* 2 overlapped regions have invalid mem type combination, */
            /* need to check whether there is a third region which has type */
            /* of UNCACHABLE and contains at least one of these two regions. */
            /* If there is, then the combination of these 3 region is valid */
            for ( j = 0; j < saved_state->num_var_mtrrs; j++ ) {
                const mtrr_physbase_t *base_j
                        = &saved_state->mtrr_physbases[j];
                const mtrr_physmask_t *mask_j
                        = &saved_state->mtrr_physmasks[j];

                if ( mask_j->v == 0 )
                    continue;

                if ( base_j->type != MTRR_TYPE_UNCACHABLE )
                    continue;

                if ( (base_ndx->base & mask_ndx->mask & mask_j->mask & maxphyaddr_mask)
                        == (base_j->base & mask_j->mask & maxphyaddr_mask)
                     && (mask_j->mask & ~mask_ndx->mask & maxphyaddr_mask) == 0 )
                    break;

                if ( (base_i->base & mask_i->mask & mask_j->mask & maxphyaddr_mask)
                        == (base_j->base & mask_j->mask & maxphyaddr_mask)
                     && (mask_j->mask & ~mask_i->mask & maxphyaddr_mask) == 0 )
                    break;
            }
            if ( j < saved_state->num_var_mtrrs )
                continue;

            printf("var MTRRs overlaping regions, invalid type combinations\n");
            print_mtrrs(saved_state);
            return false;
        }
    }

    /* XMHF: Remove call to validate_mmio_regions() in validate_mtrrs()
    if ( !validate_mmio_regions(saved_state) ) {
        printf("Some mmio region should be UC type\n");
        print_mtrrs(saved_state);
        return false;
    }
    */

    print_mtrrs(saved_state);
    return true;
}

void restore_mtrrs(const mtrr_state_t *saved_state)
{
    /* called by apply_policy() so use saved ptr */
    // XMHF: Remove use of global variable g_saved_mtrrs.
    //if ( saved_state == NULL )
    //    saved_state = g_saved_mtrrs;
    /* haven't saved them yet, so return */
    if ( saved_state == NULL )
        return;

    /* disable all MTRRs first */
    set_all_mtrrs(false);

    /* physmask's and physbase's */
    for ( unsigned int ndx = 0; ndx < saved_state->num_var_mtrrs; ndx++ ) {
        wrmsr64(MTRR_PHYS_MASK0_MSR + ndx*2,
              saved_state->mtrr_physmasks[ndx].raw);
        wrmsr64(MTRR_PHYS_BASE0_MSR + ndx*2,
              saved_state->mtrr_physbases[ndx].raw);
    }

    /* IA32_MTRR_DEF_TYPE MSR */
    wrmsr64(MSR_MTRRdefType, saved_state->mtrr_def_type.raw);
}

/* enable/disable all MTRRs */
void set_all_mtrrs(bool enable)
{
    mtrr_def_type_t mtrr_def_type;

    mtrr_def_type.raw = rdmsr64(MSR_MTRRdefType);
    mtrr_def_type.e = enable ? 1 : 0;
    wrmsr64(MSR_MTRRdefType, mtrr_def_type.raw);
}

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil * End:
 */
