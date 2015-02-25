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


void xmhfhw_cpu_cpuid(u32 op, u32 *eax, u32 *ebx, u32 *ecx, u32 *edx){
    asm volatile(
                 "cpuid \r\n"
                :"=a"(*(eax)), "=b"(*(ebx)), "=c"(*(ecx)), "=d"(*(edx))
                :"a"(op), "c"(*(ecx))
                :
               );


}


uint64_t rdtsc64(void)
{
        uint64_t rv;

        __asm__ __volatile__ ("rdtsc" : "=A" (rv));
        return (rv);
}


/* Calls to read and write control registers */
u64 read_cr0(void){
  u64 __cr0;
  asm volatile("mov %%cr0,%0 \r\n" :"=r" (__cr0));
  return __cr0;
}

void write_cr0(u64 val){
  asm volatile("mov %0,%%cr0 \r\n": :"r" (val));
}

u64 read_cr3(void){
  u64 __cr3;
  asm volatile("mov %%cr3,%0 \r\n" :"=r" (__cr3));
  return __cr3;
}


u64 read_rsp(void){
  u64 __rsp;
/*
  // TODO: x86_64 --> x86
  asm volatile("movq %%rsp,%0\n\t" :"=r" (__rsp));
*/
  asm volatile("mov %%esp,%0\n\t" :"=r" (__rsp));

  return __rsp;
}

void write_cr3(u64 val){
  asm volatile("mov %0,%%cr3 \r\n"::"r" (val));
}

u64 read_cr4(void){
  u64 __cr4;
  asm volatile("mov %%cr4, %0 \r\n" :"=r" (__cr4));
  return __cr4;
}

void write_cr4(u64 val){
  asm volatile("mov %0,%%cr4": :"r" (val));
}


/*void skinit(unsigned long eax) {
    __asm__("mov %0, %%eax": :"r" (eax));
    __asm__("skinit %%eax":);
}*/


//segment register access
u32 read_segreg_cs(void){
  u32 __cs;
  __asm__("mov %%cs, %0 \r\n" :"=r" (__cs));
  return __cs;
}

u32 read_segreg_ds(void){
  u32 __ds;
  __asm__("mov %%ds, %0 \r\n" :"=r" (__ds));
  return __ds;
}

u32 read_segreg_es(void){
  u32 __es;
  __asm__("mov %%es, %0 \r\n" :"=r" (__es));
  return __es;
}

u32 read_segreg_fs(void){
  u32 __fs;
  __asm__("mov %%fs, %0 \r\n" :"=r" (__fs));
  return __fs;
}

u32 read_segreg_gs(void){
  u32 __gs;
  __asm__("mov %%gs, %0 \r\n" :"=r" (__gs));
  return __gs;
}

u32 read_segreg_ss(void){
  u32 __ss;
  __asm__("mov %%ss, %0 \r\n" :"=r" (__ss));
  return __ss;
}

u16 read_tr_sel(void){
  u16 __trsel;
  __asm__("str %0 \r\n" :"=r" (__trsel));
  return __trsel;
}

void wbinvd(void)
{
    __asm__ __volatile__ ("wbinvd");
}

uint32_t bsrl(uint32_t mask)
{
    uint32_t   result;

    __asm__ __volatile__ ("bsrl %1,%0" : "=r" (result) : "rm" (mask) : "cc");
    return (result);
}


void xmhfhw_cpu_disable_intr(void){
    asm volatile ("cli \r\n");
}

void enable_intr(void)
{
    __asm__ __volatile__ ("sti");
}

//get extended control register (xcr)
u64 xgetbv(u32 xcr_reg){
	u32 eax, edx;

	asm volatile(".byte 0x0f,0x01,0xd0"
			: "=a" (eax), "=d" (edx)
			: "c" (xcr_reg));

	return ((u64)edx << 32) + (u64)eax;
}

//set extended control register (xcr)
void xsetbv(u32 xcr_reg, u64 value){
	u32 eax = (u32)value;
	u32 edx = value >> 32;

	asm volatile(".byte 0x0f,0x01,0xd1"
			:
			: "a" (eax), "d" (edx), "c" (xcr_reg));
}


void sysexitq(u64 rip, u64 rsp){

/*
    //TODO: x86_64 --> x86
            asm volatile(
                 "movq %0, %%rdx \r\n"
                 "movq %1, %%rcx \r\n"

                 "sysexitq \r\n"
                 //"int $0x03 \r\n"
                 //"1: jmp 1b \r\n"
                :
                : "m" (rip),
                  "m" (rsp)
                : "rdx", "rcx"
            );
*/

}


void spin_lock(volatile u32 *lock){
        __asm__ __volatile__ (
            "1:	btl	$0, %0	\r\n"	//mutex is available?
            "		jnc 1b	\r\n"	//wait till it is
            "      	lock		\r\n"   //lock the bus (exclusive access)
            "		btrl	$0, %0	\r\n"   //and try to grab the mutex
            "		jnc	1b	\r\n"   //spin until successful --> spinlock :p
            : //no asm outputs
            : "m" (*lock)
        );
    }

void spin_unlock(volatile u32 *lock){
        __asm__ __volatile__ (
            "btsl	$0, %0		\r\n"	//release spinlock
            : //no asm outputs
            : "m" (*lock)
        );
    }



u64 xmhf_baseplatform_arch_x86_getgdtbase(void){
		struct {
			u16 limit;
			u64 base;
		} __attribute__ ((packed)) gdtr;


		asm volatile(
			"sgdt %0 \r\n"
			: //no output
			: "m" (gdtr)
			: //no clobber
		);

		return gdtr.base;
}

u64 xmhf_baseplatform_arch_x86_getidtbase(void){
		struct {
			u16 limit;
			u64 base;
		} __attribute__ ((packed)) idtr;


		asm volatile(
			"sidt %0 \r\n"
			: //no output
			: "m" (idtr)
			: //no clobber
		);

		return idtr.base;
}

u64  xmhf_baseplatform_arch_x86_gettssbase(void){
	  u64 gdtbase = xmhf_baseplatform_arch_x86_getgdtbase();
	  u32 tssdesc_low, tssdesc_high;

	  asm volatile(
            "movl %2, %%edi\r\n"
            "xorl %%eax, %%eax\r\n"
            "str %%ax \r\n"
            "addl %%eax, %%edi\r\n"		//%edi is pointer to TSS descriptor in GDT
            "movl (%%edi), %0 \r\n"		//move low 32-bits of TSS descriptor into tssdesc_low
            "addl $0x4, %%edi\r\n"		//%edi points to top 32-bits of 64-bit TSS desc.
            "movl (%%edi), %1 \r\n"		//move high 32-bits of TSS descriptor into tssdesc_high
	     : "=r" (tssdesc_low), "=r" (tssdesc_high)
	     : "m"(gdtbase)
	     : "edi", "eax"
	  );

       return (  (u64)(  ((u32)tssdesc_high & 0xFF000000UL) | (((u32)tssdesc_high & 0x000000FFUL) << 16)  | ((u32)tssdesc_low >> 16)  ) );
}


int fls(int mask)
{
    return (mask == 0 ? mask : (int)bsrl((u32)mask) + 1);
}



u32 get_cpu_vendor_or_die(void) {
	    u32 dummy;
	    u32 vendor_dword1, vendor_dword2, vendor_dword3;

	    xmhfhw_cpu_cpuid(0, &dummy, &vendor_dword1, &vendor_dword3, &vendor_dword2);
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
bool xmhf_baseplatform_arch_x86_cpuhasxsavefeature(void){
	u32 eax, ebx, ecx, edx;

	//bit 26 of ECX is 1 in CPUID function 0x00000001 if
	//XSAVE/XRSTOR feature is available

	xmhfhw_cpu_cpuid(0x00000001, &eax, &ebx, &ecx, &edx);

	if((ecx & (1UL << 26)))
		return true;
	else
		return false;

}


//*
//get CPU vendor
u32 xmhf_baseplatform_arch_x86_getcpuvendor(void){
	u32 reserved, vendor_dword1, vendor_dword2, vendor_dword3;
	u32 cpu_vendor;

    xmhfhw_cpu_cpuid(0, &reserved, &vendor_dword1, &vendor_dword3, &vendor_dword2);

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
u32 xmhf_baseplatform_arch_getcpuvendor(void){
	return xmhf_baseplatform_arch_x86_getcpuvendor();
}

uint64_t read_pub_config_reg(uint32_t reg)
{
    return read_config_reg(TXT_PUB_CONFIG_REGS_BASE, reg);
}

void write_pub_config_reg(uint32_t reg, uint64_t val)
{
    write_config_reg(TXT_PUB_CONFIG_REGS_BASE, reg, val);
}

uint64_t read_priv_config_reg(uint32_t reg)
{
    return read_config_reg(TXT_PRIV_CONFIG_REGS_BASE, reg);
}

void write_priv_config_reg(uint32_t reg, uint64_t val)
{
    write_config_reg(TXT_PRIV_CONFIG_REGS_BASE, reg, val);
}

bool txt_is_launched(void)
{
    txt_sts_t sts;

    sts._raw = read_pub_config_reg(TXTCR_STS);

    return sts.senter_done_sts;
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



void print_mtrrs(const mtrr_state_t *saved_state)
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

void xmhfhw_cpu_x86_save_mtrrs(mtrr_state_t *saved_state)
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



bool validate_mtrrs(const mtrr_state_t *saved_state)
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

void xmhfhw_cpu_x86_restore_mtrrs(mtrr_state_t *saved_state)
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






txt_heap_t *get_txt_heap(void)
{
    return (txt_heap_t *)(unsigned long)read_pub_config_reg(TXTCR_HEAP_BASE);
}

uint64_t get_bios_data_size(txt_heap_t *heap)
{
    return *(uint64_t *)heap;
    //return xmhf_arch_baseplatform_flat_readu64((u32)heap);
}

bios_data_t *get_bios_data_start(txt_heap_t *heap)
{
    return (bios_data_t *)((char*)heap + sizeof(uint64_t));
}

uint64_t get_os_mle_data_size(txt_heap_t *heap)
{
    return *(uint64_t *)(heap + get_bios_data_size(heap));
    //return xmhf_arch_baseplatform_flat_readu64((u32)(heap + get_bios_data_size(heap)));
}

os_mle_data_t *get_os_mle_data_start(txt_heap_t *heap)
{
    return (os_mle_data_t *)(heap + get_bios_data_size(heap) +
                              sizeof(uint64_t));
}

uint64_t get_os_sinit_data_size(txt_heap_t *heap)
{
    return *(uint64_t *)(heap + get_bios_data_size(heap) +
                         get_os_mle_data_size(heap));
    //return xmhf_arch_baseplatform_flat_readu64((u32)(heap + get_bios_data_size(heap) +
    //                     get_os_mle_data_size(heap)));

}

os_sinit_data_t *get_os_sinit_data_start(txt_heap_t *heap)
{
    return (os_sinit_data_t *)(heap + get_bios_data_size(heap) +
                               get_os_mle_data_size(heap) +
                               sizeof(uint64_t));
}

uint64_t get_sinit_mle_data_size(txt_heap_t *heap)
{
    return *(uint64_t *)(heap + get_bios_data_size(heap) +
                         get_os_mle_data_size(heap) +
                         get_os_sinit_data_size(heap));
    //return xmhf_arch_baseplatform_flat_readu64((u32)(heap + get_bios_data_size(heap) +
    //                     get_os_mle_data_size(heap) +
    //                     get_os_sinit_data_size(heap)));
}

sinit_mle_data_t *get_sinit_mle_data_start(txt_heap_t *heap)
{
    return (sinit_mle_data_t *)(heap + get_bios_data_size(heap) +
                                get_os_mle_data_size(heap) +
                                get_os_sinit_data_size(heap) +
                                sizeof(uint64_t));
}


