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

//xmhfhw_cpu - base CPU functions
//author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfhw.h>
#include <xmhf-debug.h>



/*
 * set the memory type for specified range (base to base+size)
 * to mem_type and everything else to UC
 */
bool set_mem_type(u8 *base, uint32_t size, uint32_t mem_type)
{
    int num_pages;
    int ndx;
    mtrr_def_type_t mtrr_def_type;
    mtrr_cap_t mtrr_cap;
    mtrr_physmask_t mtrr_physmask;
    mtrr_physbase_t mtrr_physbase;

    _XDPRINTF_("%s: %u\n", __func__, __LINE__);

    /*
     * disable all fixed MTRRs
     * set default type to UC
     */
    //mtrr_def_type.raw = CASM_FUNCCALL(rdmsr64,MSR_MTRRdefType);
    unpack_mtrr_def_type_t(&mtrr_def_type, CASM_FUNCCALL(rdmsr64,MSR_MTRRdefType));
    mtrr_def_type.fe = 0;
    mtrr_def_type.type = MTRR_TYPE_UNCACHABLE;
 CASM_FUNCCALL(wrmsr64,MSR_MTRRdefType, pack_mtrr_def_type_t(&mtrr_def_type));

    _XDPRINTF_("%s: %u\n", __func__, __LINE__);

    /*
     * initially disable all variable MTRRs (we'll enable the ones we use)
     */
    //mtrr_cap.raw = CASM_FUNCCALL(rdmsr64,MSR_MTRRcap);
    unpack_mtrr_cap_t(&mtrr_cap, CASM_FUNCCALL(rdmsr64,MSR_MTRRcap));
    for ( ndx = 0; ndx < mtrr_cap.vcnt; ndx++ ) {
        //mtrr_physmask.raw = CASM_FUNCCALL(rdmsr64,MTRR_PHYS_MASK0_MSR + ndx*2);
        unpack_mtrr_physmask_t(&mtrr_physmask, CASM_FUNCCALL(rdmsr64,MTRR_PHYS_MASK0_MSR + ndx*2));
        mtrr_physmask.v = 0;
 CASM_FUNCCALL(wrmsr64,MTRR_PHYS_MASK0_MSR + ndx*2, pack_mtrr_physmask_t(&mtrr_physmask));
    }

    _XDPRINTF_("%s: %u\n", __func__, __LINE__);

    /*
     * map all AC module pages as mem_type
     */

    num_pages = (size + PAGE_SIZE_4K - 1) >> PAGE_SHIFT_4K;
    ndx = 0;

    _XDPRINTF_("setting MTRRs for acmod: base=%p, size=%x, num_pages=%d\n",
           base, size, num_pages);

    while ( num_pages > 0 ) {
        uint32_t pages_in_range;

        /* set the base of the current MTRR */
        //mtrr_physbase.raw = CASM_FUNCCALL(rdmsr64,MTRR_PHYS_BASE0_MSR + ndx*2);
        unpack_mtrr_physbase_t(&mtrr_physbase, CASM_FUNCCALL(rdmsr64,MTRR_PHYS_BASE0_MSR + ndx*2));

        mtrr_physbase.reserved1 = 0;
        mtrr_physbase.base = (unsigned long)base >> PAGE_SHIFT_4K;
        mtrr_physbase.type = mem_type;
        /* set explicitly in case base field is >24b (MAXPHYADDR >36) */
        mtrr_physbase.reserved2 = 0;

        _XDPRINTF_("%s: %u writing %016llx\n", __func__, __LINE__,
                   pack_mtrr_physbase_t(&mtrr_physbase));

 CASM_FUNCCALL(wrmsr64,MTRR_PHYS_BASE0_MSR + ndx*2, pack_mtrr_physbase_t(&mtrr_physbase));

        _XDPRINTF_("%s: %u\n", __func__, __LINE__);

        /*
         * calculate MTRR mask
         * MTRRs can map pages in power of 2
         * may need to use multiple MTRRS to map all of region
         */
        pages_in_range = 1 << (fls(num_pages) - 1);

        _XDPRINTF_("%s: %u pages_in_range=%u\n", __func__, __LINE__, pages_in_range);

        //mtrr_physmask.raw = CASM_FUNCCALL(rdmsr64,MTRR_PHYS_MASK0_MSR + ndx*2);
        unpack_mtrr_physmask_t(&mtrr_physmask, CASM_FUNCCALL(rdmsr64,MTRR_PHYS_MASK0_MSR + ndx*2));

        mtrr_physmask.reserved1 = 0;
        mtrr_physmask.mask = (u32) ~(pages_in_range - 1);
        mtrr_physmask.v = 1;
        /* set explicitly in case mask field is >24b (MAXPHYADDR >36) */
        mtrr_physmask.reserved2 = 0;

        _XDPRINTF_("%s: %u writing %016llx\n", __func__, __LINE__,
                   pack_mtrr_physmask_t(&mtrr_physmask));

 CASM_FUNCCALL(wrmsr64,MTRR_PHYS_MASK0_MSR + ndx*2, pack_mtrr_physmask_t(&mtrr_physmask));

        _XDPRINTF_("%s: %u\n", __func__, __LINE__);

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
            _XDPRINTF_("exceeded number of var MTRRs when mapping range\n");
            return false;
        }
    }

    _XDPRINTF_("%s: %u\n", __func__, __LINE__);

    return true;
}

