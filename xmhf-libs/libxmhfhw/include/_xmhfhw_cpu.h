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

//_cpu.h - CPU declarations
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHFHW_CPU_H__
#define __XMHFHW_CPU_H__

#ifndef __ASSEMBLY__


//from _processor.h
typedef struct {
    mtrr_def_type_t	    mtrr_def_type;
    int	                num_var_mtrrs;
    mtrr_physbase_t     mtrr_physbases[MAX_VARIABLE_MTRRS];
    mtrr_physmask_t     mtrr_physmasks[MAX_VARIABLE_MTRRS];
} __attribute__((packed)) mtrr_state_t;


static inline int fls(int mask)
{
    return (mask == 0 ? mask : (int)bsrl((u32)mask) + 1);
}



	static inline u32 get_cpu_vendor_or_die(void) {
	    u32 dummy;
	    u32 vendor_dword1, vendor_dword2, vendor_dword3;

	    cpuid(0, &dummy, &vendor_dword1, &vendor_dword3, &vendor_dword2);
	    if(vendor_dword1 == AMD_STRING_DWORD1 && vendor_dword2 == AMD_STRING_DWORD2
	       && vendor_dword3 == AMD_STRING_DWORD3)
		return CPU_VENDOR_AMD;
	    else if(vendor_dword1 == INTEL_STRING_DWORD1 && vendor_dword2 == INTEL_STRING_DWORD2
		    && vendor_dword3 == INTEL_STRING_DWORD3)
		return CPU_VENDOR_INTEL;
	    else
		HALT();

	    return 0; // never reached
	}


//*
//returns true if CPU has support for XSAVE/XRSTOR
static inline bool xmhf_baseplatform_arch_x86_cpuhasxsavefeature(void){
	u32 eax, ebx, ecx, edx;

	//bit 26 of ECX is 1 in CPUID function 0x00000001 if
	//XSAVE/XRSTOR feature is available

	cpuid(0x00000001, &eax, &ebx, &ecx, &edx);

	if((ecx & (1UL << 26)))
		return true;
	else
		return false;

}

static inline u32 xmhf_baseplatform_arch_x86_getcpulapicid(void){
  u32 eax, edx, *lapic_reg;
  u32 lapic_id;

  //read LAPIC id of this core
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  //if (edx != 0 ){ //APIC is not below 4G, unsupported
  //	_XDPRINTF_("%s: APIC is not below 4G, unsupported. Halting!", __FUNCTION__);
  //	HALT();
  //}
  eax &= (u32)0xFFFFF000UL;
  lapic_reg = (u32 *)((u32)eax+ (u32)LAPIC_ID);
  lapic_id = xmhfhw_sysmemaccess_readu32((u32)lapic_reg);
  lapic_id = lapic_id >> 24;

  return lapic_id;
}




//*
//get CPU vendor
static inline u32 xmhf_baseplatform_arch_x86_getcpuvendor(void){
	u32 reserved, vendor_dword1, vendor_dword2, vendor_dword3;
	u32 cpu_vendor;

    cpuid(0, &reserved, &vendor_dword1, &vendor_dword3, &vendor_dword2);

	if(vendor_dword1 == AMD_STRING_DWORD1 && vendor_dword2 == AMD_STRING_DWORD2
			&& vendor_dword3 == AMD_STRING_DWORD3)
		cpu_vendor = CPU_VENDOR_AMD;
	else if(vendor_dword1 == INTEL_STRING_DWORD1 && vendor_dword2 == INTEL_STRING_DWORD2
			&& vendor_dword3 == INTEL_STRING_DWORD3)
		cpu_vendor = CPU_VENDOR_INTEL;
	else{
		cpu_vendor = CPU_VENDOR_UNKNOWN;
		//_XDPRINTF_("%s: unrecognized x86 CPU (0x%08x:0x%08x:0x%08x). HALT!\n",
		//	__FUNCTION__, vendor_dword1, vendor_dword2, vendor_dword3);
		//HALT();
	}

	return cpu_vendor;
}

//*
static inline u32 xmhf_baseplatform_arch_getcpuvendor(void){
	return xmhf_baseplatform_arch_x86_getcpuvendor();
}











//from _txt_config_regs.h
static inline uint64_t read_pub_config_reg(uint32_t reg)
{
    return read_config_reg(TXT_PUB_CONFIG_REGS_BASE, reg);
}

static inline void write_pub_config_reg(uint32_t reg, uint64_t val)
{
    write_config_reg(TXT_PUB_CONFIG_REGS_BASE, reg, val);
}

static inline uint64_t read_priv_config_reg(uint32_t reg)
{
    return read_config_reg(TXT_PRIV_CONFIG_REGS_BASE, reg);
}

static inline void write_priv_config_reg(uint32_t reg, uint64_t val)
{
    write_config_reg(TXT_PRIV_CONFIG_REGS_BASE, reg, val);
}





//from _txt_smx.h
static inline bool txt_is_launched(void)
{
    txt_sts_t sts;

    sts._raw = read_pub_config_reg(TXTCR_STS);

    return sts.senter_done_sts;
}












//from _txt_mtrrs.h

/* enable/disable all MTRRs */
static inline void set_all_mtrrs(bool enable)
{
    mtrr_def_type_t mtrr_def_type;

    mtrr_def_type.raw = rdmsr64(MSR_MTRRdefType);
    mtrr_def_type.e = enable ? 1 : 0;
    wrmsr64(MSR_MTRRdefType, mtrr_def_type.raw);
}


/*
 * set the memory type for specified range (base to base+size)
 * to mem_type and everything else to UC
 */
static inline bool set_mem_type(void *base, uint32_t size, uint32_t mem_type)
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

    //_XDPRINTF_("setting MTRRs for acmod: base=%p, size=%x, num_pages=%d\n",
    //       base, size, num_pages);

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
            //_XDPRINTF_("exceeded number of var MTRRs when mapping range\n");
            return false;
        }
    }

    return true;
}



static inline void print_mtrrs(const mtrr_state_t *saved_state)
{
    //int i;

    //_XDPRINTF_("mtrr_def_type: e = %d, fe = %d, type = %x\n",
    //       saved_state->mtrr_def_type.e, saved_state->mtrr_def_type.fe,
    //       saved_state->mtrr_def_type.type );
    //_XDPRINTF_("mtrrs:\n");
    //_XDPRINTF_("\t\tbase\tmask\ttype\tv\n");
    //for ( i = 0; i < saved_state->num_var_mtrrs; i++ ) {
    //    _XDPRINTF_("\t\t%6.6x\t%6.6x\t%2.2x\t%d\n",
    //           saved_state->mtrr_physbases[i].base,
    //           saved_state->mtrr_physmasks[i].mask,
    //           saved_state->mtrr_physbases[i].type,
    //           saved_state->mtrr_physmasks[i].v );
    //}
}

static inline void xmhfhw_cpu_x86_save_mtrrs(mtrr_state_t *saved_state)
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
        //_XDPRINTF_("actual # var MTRRs (%d) > MAX_VARIABLE_MTRRS (%d)\n",
        //       mtrr_cap.vcnt, MAX_VARIABLE_MTRRS);
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

    //g_saved_mtrrs = saved_state;
}



static inline bool validate_mtrrs(const mtrr_state_t *saved_state)
{
    mtrr_cap_t mtrr_cap;
    int ndx;

    /* check is meaningless if MTRRs were disabled */
    if ( saved_state->mtrr_def_type.e == 0 )
        return true;

    //print_mtrrs(saved_state);

    /* number variable MTRRs */
    mtrr_cap.raw = rdmsr64(MSR_MTRRcap);
    if ( mtrr_cap.vcnt < saved_state->num_var_mtrrs ) {
        //_XDPRINTF_("actual # var MTRRs (%d) < saved # (%d)\n",
        //       mtrr_cap.vcnt, saved_state->num_var_mtrrs);
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
            //_XDPRINTF_("var MTRRs with non-contiguous regions: "
            //       "base=%06x, mask=%06x\n",
            //       (unsigned int) saved_state->mtrr_physbases[ndx].base,
            //       (unsigned int) saved_state->mtrr_physmasks[ndx].mask);
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

            //_XDPRINTF_("var MTRRs overlaping regions, invalid type combinations\n");
            print_mtrrs(saved_state);
            return false;
        }
    }


    return true;
}

static inline void xmhfhw_cpu_x86_restore_mtrrs(mtrr_state_t *saved_state)
{
    int ndx;

    //if(NULL == saved_state) {
        //_XDPRINTF_("\nFATAL ERROR: restore_mtrrs(): called with NULL\n");
        //HALT();
    //    return;
    //}

    //print_mtrrs(saved_state);

    /* called by apply_policy() so use saved ptr */
    //if ( saved_state == NULL )
    //    saved_state = g_saved_mtrrs;
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












//from _txt_heap.h

/*
 * OS/loader to MLE structure
 *   - private to tboot (so can be any format we need)
 */
#define MAX_LCP_PO_DATA_SIZE     64*1024  /* 64k */

typedef struct {
    uint32_t          version;           /* currently 2 */
    mtrr_state_t      saved_mtrr_state;  /* saved prior to changes for SINIT */
    //multiboot_info_t* mbi;               /* needs to be restored to ebx */
    void *mbi;
    uint32_t          saved_misc_enable_msr;  /* saved prior to SENTER */
                                         /* PO policy data */
    uint8_t           lcp_po_data[MAX_LCP_PO_DATA_SIZE];
} __attribute__ ((packed)) os_mle_data_t;


/*
 * TXT heap data format and field accessor fns
 */

/*
 * offset                 length                      field
 * ------                 ------                      -----
 *  0                      8                          bios_data_size
 *  8                      bios_data_size - 8      bios_data
 *
 *  bios_data_size      8                          os_mle_data_size
 *  bios_data_size +    os_mle_data_size - 8       os_mle_data
 *   8
 *
 *  bios_data_size +    8                          os_sinit_data_size
 *   os_mle_data_size
 *  bios_data_size +    os_sinit_data_size - 8     os_sinit_data
 *   os_mle_data_size +
 *   8
 *
 *  bios_data_size +    8                          sinit_mle_data_size
 *   os_mle_data_size +
 *   os_sinit_data_size
 *  bios_data_size +    sinit_mle_data_size - 8    sinit_mle_data
 *   os_mle_data_size +
 *   os_sinit_data_size +
 *   8
 */


/* this is a common use with annoying casting, so make it an inline */
static inline txt_heap_t *get_txt_heap(void)
{
    return (txt_heap_t *)(unsigned long)read_pub_config_reg(TXTCR_HEAP_BASE);
}

static inline uint64_t get_bios_data_size(txt_heap_t *heap)
{
    return *(uint64_t *)heap;
    //return xmhf_arch_baseplatform_flat_readu64((u32)heap);
}

static inline bios_data_t *get_bios_data_start(txt_heap_t *heap)
{
    return (bios_data_t *)((char*)heap + sizeof(uint64_t));
}

static inline uint64_t get_os_mle_data_size(txt_heap_t *heap)
{
    return *(uint64_t *)(heap + get_bios_data_size(heap));
    //return xmhf_arch_baseplatform_flat_readu64((u32)(heap + get_bios_data_size(heap)));
}

static inline os_mle_data_t *get_os_mle_data_start(txt_heap_t *heap)
{
    return (os_mle_data_t *)(heap + get_bios_data_size(heap) +
                              sizeof(uint64_t));
}

static inline uint64_t get_os_sinit_data_size(txt_heap_t *heap)
{
    return *(uint64_t *)(heap + get_bios_data_size(heap) +
                         get_os_mle_data_size(heap));
    //return xmhf_arch_baseplatform_flat_readu64((u32)(heap + get_bios_data_size(heap) +
    //                     get_os_mle_data_size(heap)));

}

static inline os_sinit_data_t *get_os_sinit_data_start(txt_heap_t *heap)
{
    return (os_sinit_data_t *)(heap + get_bios_data_size(heap) +
                               get_os_mle_data_size(heap) +
                               sizeof(uint64_t));
}

static inline uint64_t get_sinit_mle_data_size(txt_heap_t *heap)
{
    return *(uint64_t *)(heap + get_bios_data_size(heap) +
                         get_os_mle_data_size(heap) +
                         get_os_sinit_data_size(heap));
    //return xmhf_arch_baseplatform_flat_readu64((u32)(heap + get_bios_data_size(heap) +
    //                     get_os_mle_data_size(heap) +
    //                     get_os_sinit_data_size(heap)));
}

static inline sinit_mle_data_t *get_sinit_mle_data_start(txt_heap_t *heap)
{
    return (sinit_mle_data_t *)(heap + get_bios_data_size(heap) +
                                get_os_mle_data_size(heap) +
                                get_os_sinit_data_size(heap) +
                                sizeof(uint64_t));
}


#endif //__ASSEMBLY__

#endif // __XMHFHW_CPU_H__
