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

/*
 * Modified for XMHF by jonmccune@cmu.edu, 2011.01.05
 */

#include <xmhf.h> 

#define MTRR_TYPE_MIXED         -1
#define MMIO_APIC_BASE          0xFEE00000
#define NR_MMIO_APIC_PAGES      1
#define NR_MMIO_IOAPIC_PAGES    1
#define NR_MMIO_PCICFG_PAGES    1

/* saved MTRR state or NULL if orig. MTRRs have not been changed */
//static __data mtrr_state_t *g_saved_mtrrs = NULL;
static mtrr_state_t *g_saved_mtrrs = NULL;

/*
 * this must be done for each processor so that all have the same
 * memory types
 */
bool set_mtrrs_for_acmod(acm_hdr_t *hdr)
{
    unsigned long eflags;
    unsigned long cr0, cr4;

    /*
     * need to do some things before we start changing MTRRs
     *
     * since this will modify some of the MTRRs, they should be saved first
     * so that they can be restored once the AC mod is done
     */

    /* disable interrupts */
    get_eflags(eflags);
    disable_intr();

    /* save CR0 then disable cache (CRO.CD=1, CR0.NW=0) */
    cr0 = read_cr0();
    write_cr0((cr0 & ~CR0_NW) | CR0_CD);

    /* flush caches */
    wbinvd();

    /* save CR4 and disable global pages (CR4.PGE=0) */
    cr4 = read_cr4();
    write_cr4(cr4 & ~CR4_PGE);

    /* disable MTRRs */
    set_all_mtrrs(false);

    /*
     * now set MTRRs for AC mod and rest of memory
     */
    if ( !set_mem_type(hdr, hdr->size*4, MTRR_TYPE_WRBACK) )
        return false;

    /*
     * now undo some of earlier changes and enable our new settings
     */

    /* flush caches */
    wbinvd();

    /* enable MTRRs */
    set_all_mtrrs(true);

    /* restore CR0 (cacheing) */
    write_cr0(cr0);

    /* restore CR4 (global pages) */
    write_cr4(cr4);

    /* enable interrupts */
    set_eflags(eflags);


    return true;
}

void print_mtrrs(const mtrr_state_t *saved_state)
{
    int i;
    
    printf("mtrr_def_type: e = %d, fe = %d, type = %x\n",
           saved_state->mtrr_def_type.e, saved_state->mtrr_def_type.fe,
           saved_state->mtrr_def_type.type );
    printf("mtrrs:\n");
    printf("\t\tbase\tmask\ttype\tv\n");
    for ( i = 0; i < saved_state->num_var_mtrrs; i++ ) {
        printf("\t\t%6.6x\t%6.6x\t%2.2x\t%d\n",
               saved_state->mtrr_physbases[i].base,
               saved_state->mtrr_physmasks[i].mask,
               saved_state->mtrr_physbases[i].type,
               saved_state->mtrr_physmasks[i].v );
    }
}

void save_mtrrs(mtrr_state_t *saved_state)
{
    mtrr_cap_t mtrr_cap;
    int ndx;

    /* IA32_MTRR_DEF_TYPE MSR */
    saved_state->mtrr_def_type.raw = rdmsr64(MSR_MTRRdefType);

    /* number variable MTTRRs */
    mtrr_cap.raw = rdmsr64(MSR_MTRRcap);
    if ( mtrr_cap.vcnt > MAX_VARIABLE_MTRRS ) {
        /* print warning but continue saving what we can */
        /* (set_mem_type() won't exceed the array, so we're safe doing this) */
        printf("actual # var MTRRs (%d) > MAX_VARIABLE_MTRRS (%d)\n",
               mtrr_cap.vcnt, MAX_VARIABLE_MTRRS);
        saved_state->num_var_mtrrs = MAX_VARIABLE_MTRRS;
    }
    else
        saved_state->num_var_mtrrs = mtrr_cap.vcnt;

    /* physmask's and physbase's */
    for ( ndx = 0; ndx < saved_state->num_var_mtrrs; ndx++ ) {
        saved_state->mtrr_physmasks[ndx].raw =
            rdmsr64(MTRR_PHYS_MASK0_MSR + ndx*2);
        saved_state->mtrr_physbases[ndx].raw =
            rdmsr64(MTRR_PHYS_BASE0_MSR + ndx*2);
    }

    print_mtrrs(saved_state);
    
    g_saved_mtrrs = saved_state;
}

#if 0 /* functions unused as of 2011-07-19 */
/* base should be 4k-bytes aligned, no invalid overlap combination */
static int get_page_type(const mtrr_state_t *saved_state, uint32_t base)
{
    int type = -1;
    bool wt = false;
    int i;

    /* omit whether the fix mtrrs are enabled, just check var mtrrs */

    base >>= PAGE_SHIFT_4K;
    for ( i = 0; i < saved_state->num_var_mtrrs; i++ ) {
        const mtrr_physbase_t *base_i = &saved_state->mtrr_physbases[i];
        const mtrr_physmask_t *mask_i = &saved_state->mtrr_physmasks[i];

        if ( mask_i->v == 0 )
            continue;
        if ( (base & mask_i->mask) != (uint32_t)(base_i->base & mask_i->mask) )
            continue;

        type = base_i->type;
        if ( type == MTRR_TYPE_UNCACHABLE )
            return MTRR_TYPE_UNCACHABLE;
        if ( type == MTRR_TYPE_WRTHROUGH )
            wt = true;
    }
    if ( wt )
        return MTRR_TYPE_WRTHROUGH;
    if ( type != -1 )
        return type;

    return saved_state->mtrr_def_type.type;
}

static int get_region_type(const mtrr_state_t *saved_state,
                           uint32_t base, uint32_t pages)
{
    int type;
    uint32_t end;

    if ( pages == 0 )
        return MTRR_TYPE_MIXED;

    /* wrap the 4G address space */
    if ( ((uint32_t)(~0) - base) < (pages << PAGE_SHIFT_4K) )
        return MTRR_TYPE_MIXED;

    if ( saved_state->mtrr_def_type.e == 0 )
        return MTRR_TYPE_UNCACHABLE;

    /* align to 4k page boundary */    
    base = PAGE_ALIGN_4K(base); //base &= PAGE_MASK;
    end = base + (pages << PAGE_SHIFT_4K);

    type = get_page_type(saved_state, base);
    base += PAGE_SIZE_4K;
    for ( ; base < end; base += PAGE_SIZE_4K )
        if ( type != get_page_type(saved_state, base) )
            return MTRR_TYPE_MIXED;

    return type;
}
#endif

/* static bool validate_mmio_regions(const mtrr_state_t *saved_state) */
/* { */
/*     acpi_table_mcfg_t *acpi_table_mcfg; */
/*     acpi_table_ioapic_t *acpi_table_ioapic; */

/*     /\* mmio space for TXT private config space should be UC *\/ */
/*     if ( get_region_type(saved_state, TXT_PRIV_CONFIG_REGS_BASE, */
/*                          NR_TXT_CONFIG_PAGES) */
/*            != MTRR_TYPE_UNCACHABLE ) { */
/*         printf("MMIO space for TXT private config space should be UC\n"); */
/*         return false; */
/*     } */

/*     /\* mmio space for TXT public config space should be UC *\/ */
/*     if ( get_region_type(saved_state, TXT_PUB_CONFIG_REGS_BASE, */
/*                          NR_TXT_CONFIG_PAGES) */
/*            != MTRR_TYPE_UNCACHABLE ) { */
/*         printf("MMIO space for TXT public config space should be UC\n"); */
/*         return false; */
/*     } */

/*     /\* mmio space for TPM should be UC *\/ */
/*     if ( get_region_type(saved_state, TPM_LOCALITY_BASE, */
/*                          NR_TPM_LOCALITY_PAGES * TPM_NR_LOCALITIES) */
/*            != MTRR_TYPE_UNCACHABLE ) { */
/*         printf("MMIO space for TPM should be UC\n"); */
/*         return false; */
/*     } */

/*     /\* mmio space for APIC should be UC *\/ */
/*     if ( get_region_type(saved_state, MMIO_APIC_BASE, NR_MMIO_APIC_PAGES) */
/*            != MTRR_TYPE_UNCACHABLE ) { */
/*         printf("MMIO space for APIC should be UC\n"); */
/*         return false; */
/*     } */

/*     /\* TBD: is this check useful if we aren't DMA protecting ACPI? *\/ */
/*     /\* mmio space for IOAPIC should be UC *\/ */
/*     acpi_table_ioapic = (acpi_table_ioapic_t *)get_acpi_ioapic_table(); */
/*     if ( acpi_table_ioapic == NULL) { */
/*         printf("acpi_table_ioapic == NULL\n"); */
/*         return false; */
/*     } */
/*     printf("acpi_table_ioapic @ %p, .address = %x\n", */
/*            acpi_table_ioapic, acpi_table_ioapic->address); */
/*     if ( get_region_type(saved_state, acpi_table_ioapic->address, */
/*                          NR_MMIO_IOAPIC_PAGES) */
/*            != MTRR_TYPE_UNCACHABLE ) { */
/*         printf("MMIO space(%x) for IOAPIC should be UC\n", */
/*                acpi_table_ioapic->address); */
/*         return false; */
/*     } */

/*     /\* TBD: is this check useful if we aren't DMA protecting ACPI? *\/ */
/*     /\* mmio space for PCI config space should be UC *\/ */
/*     acpi_table_mcfg = (acpi_table_mcfg_t *)get_acpi_mcfg_table(); */
/*     if ( acpi_table_mcfg == NULL) { */
/*         printf("acpi_table_mcfg == NULL\n"); */
/*         return false; */
/*     } */
/*     printf("acpi_table_mcfg @ %p, .base_address = %x\n", */
/*            acpi_table_mcfg, acpi_table_mcfg->base_address); */
/*     if ( get_region_type(saved_state, acpi_table_mcfg->base_address, */
/*                          NR_MMIO_PCICFG_PAGES) */
/*            != MTRR_TYPE_UNCACHABLE ) { */
/*         printf("MMIO space(%x) for PCI config space should be UC\n", */
/*                acpi_table_mcfg->base_address); */
/*         return false; */
/*     } */

/*     return true; */
/* } */

bool validate_mtrrs(const mtrr_state_t *saved_state)
{
    mtrr_cap_t mtrr_cap;
    int ndx;

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
    /* TBD: assert(MAXPHYADDR == 36); */
    for ( ndx = 0; ndx < saved_state->num_var_mtrrs; ndx++ ) {
        uint64_t tb;

        if ( saved_state->mtrr_physmasks[ndx].v == 0 )
            continue;

        for ( tb = 0x1; tb != 0x1000000; tb = tb << 1 ) {
            if ( (tb & saved_state->mtrr_physmasks[ndx].mask) != 0 )
                break;
        }
        for ( ; tb != 0x1000000; tb = tb << 1 ) {
            if ( (tb & saved_state->mtrr_physmasks[ndx].mask) == 0 )
                break;
        }
        if ( tb != 0x1000000 ) {
            printf("var MTRRs with non-contiguous regions: "
                   "base=%06x, mask=%06x\n",
                   (unsigned int) saved_state->mtrr_physbases[ndx].base,
                   (unsigned int) saved_state->mtrr_physmasks[ndx].mask);
            print_mtrrs(saved_state);
            return false;
        }
    }

    /* overlaping regions with invalid memory type combinations */
    for ( ndx = 0; ndx < saved_state->num_var_mtrrs; ndx++ ) {
        int i;
        const mtrr_physbase_t *base_ndx = &saved_state->mtrr_physbases[ndx];
        const mtrr_physmask_t *mask_ndx = &saved_state->mtrr_physmasks[ndx];

        if ( mask_ndx->v == 0 )
            continue;

        for ( i = ndx + 1; i < saved_state->num_var_mtrrs; i++ ) {
            int j;
            const mtrr_physbase_t *base_i = &saved_state->mtrr_physbases[i];
            const mtrr_physmask_t *mask_i = &saved_state->mtrr_physmasks[i];

            if ( mask_i->v == 0 )
                continue;

            if ( (base_ndx->base & mask_ndx->mask & mask_i->mask)
                    != (base_i->base & mask_i->mask)
                 && (base_i->base & mask_i->mask & mask_ndx->mask)
                    != (base_ndx->base & mask_ndx->mask) )
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

                if ( (base_ndx->base & mask_ndx->mask & mask_j->mask)
                        == (base_j->base & mask_j->mask)
                     && (mask_j->mask & ~mask_ndx->mask) == 0 )
                    break;

                if ( (base_i->base & mask_i->mask & mask_j->mask)
                        == (base_j->base & mask_j->mask)
                     && (mask_j->mask & ~mask_i->mask) == 0 )
                    break;
            }
            if ( j < saved_state->num_var_mtrrs )
                continue;

            printf("var MTRRs overlaping regions, invalid type combinations\n");
            print_mtrrs(saved_state);
            return false;
        }
    }

/*     if ( !validate_mmio_regions(saved_state) ) { */
/*         printf("Some mmio region should be UC type\n"); */
/*         print_mtrrs(saved_state); */
/*         return false; */
/*     } */

    //print_mtrrs(saved_state);
    return true;
}

void restore_mtrrs(mtrr_state_t *saved_state)
{
    int ndx;

    if(NULL == saved_state) {
        printf("\nFATAL ERROR: restore_mtrrs(): called with NULL\n");
        HALT();
    }

    //print_mtrrs(saved_state);
        
    /* called by apply_policy() so use saved ptr */
    if ( saved_state == NULL )
        saved_state = g_saved_mtrrs;
    /* haven't saved them yet, so return */
    if ( saved_state == NULL )
        return;

    /* disable all MTRRs first */
    set_all_mtrrs(false);

    /* physmask's and physbase's */
    for ( ndx = 0; ndx < saved_state->num_var_mtrrs; ndx++ ) {
        wrmsr64(MTRR_PHYS_MASK0_MSR + ndx*2,
              saved_state->mtrr_physmasks[ndx].raw);
        wrmsr64(MTRR_PHYS_BASE0_MSR + ndx*2,
              saved_state->mtrr_physbases[ndx].raw);
    }

    /* IA32_MTRR_DEF_TYPE MSR */
    wrmsr64(MSR_MTRRdefType, saved_state->mtrr_def_type.raw);
}

/*
 * set the memory type for specified range (base to base+size)
 * to mem_type and everything else to UC
 */
bool set_mem_type(void *base, uint32_t size, uint32_t mem_type)
{
    int num_pages;
    int ndx;
    mtrr_def_type_t mtrr_def_type;
    mtrr_cap_t mtrr_cap;
    mtrr_physmask_t mtrr_physmask;
    mtrr_physbase_t mtrr_physbase;

    /*
     * disable all fixed MTRRs
     * set default type to UC
     */
    mtrr_def_type.raw = rdmsr64(MSR_MTRRdefType);
    mtrr_def_type.fe = 0;
    mtrr_def_type.type = MTRR_TYPE_UNCACHABLE;
    wrmsr64(MSR_MTRRdefType, mtrr_def_type.raw);

    /*
     * initially disable all variable MTRRs (we'll enable the ones we use)
     */
    mtrr_cap.raw = rdmsr64(MSR_MTRRcap);
    for ( ndx = 0; ndx < mtrr_cap.vcnt; ndx++ ) {
        mtrr_physmask.raw = rdmsr64(MTRR_PHYS_MASK0_MSR + ndx*2);
        mtrr_physmask.v = 0;
        wrmsr64(MTRR_PHYS_MASK0_MSR + ndx*2, mtrr_physmask.raw);
    }

    /*
     * map all AC module pages as mem_type
     */

    num_pages = (size + PAGE_SIZE_4K - 1) >> PAGE_SHIFT_4K;
    ndx = 0;

    printf("setting MTRRs for acmod: base=%p, size=%x, num_pages=%d\n",
           base, size, num_pages);

    while ( num_pages > 0 ) {
        uint32_t pages_in_range;

        /* set the base of the current MTRR */
        mtrr_physbase.raw = rdmsr64(MTRR_PHYS_BASE0_MSR + ndx*2);
        mtrr_physbase.base = (unsigned long)base >> PAGE_SHIFT_4K;
        mtrr_physbase.type = mem_type;
        /* set explicitly in case base field is >24b (MAXPHYADDR >36) */
        mtrr_physbase.reserved2 = 0;
        wrmsr64(MTRR_PHYS_BASE0_MSR + ndx*2, mtrr_physbase.raw);

        /*
         * calculate MTRR mask
         * MTRRs can map pages in power of 2
         * may need to use multiple MTRRS to map all of region
         */
        pages_in_range = 1 << (fls(num_pages) - 1);

        mtrr_physmask.raw = rdmsr64(MTRR_PHYS_MASK0_MSR + ndx*2);
        mtrr_physmask.mask = ~(pages_in_range - 1);
        mtrr_physmask.v = 1;
        /* set explicitly in case mask field is >24b (MAXPHYADDR >36) */
        mtrr_physmask.reserved2 = 0;
        wrmsr64(MTRR_PHYS_MASK0_MSR + ndx*2, mtrr_physmask.raw);

        /* prepare for the next loop depending on number of pages
         * We figure out from the above how many pages could be used in this
         * mtrr. Then we decrement the count, increment the base,
         * increment the mtrr we are dealing with, and if num_pages is
         * still not zero, we do it again.
         */
        base += (pages_in_range * PAGE_SIZE_4K);
        num_pages -= pages_in_range;
        ndx++;
        if ( ndx == mtrr_cap.vcnt ) {
            printf("exceeded number of var MTRRs when mapping range\n");
            return false;
        }
    }

    return true;
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
 * indent-tabs-mode: nil
 * End:
 */
