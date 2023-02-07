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
 * txt.c: Intel(r) TXT support functions, including initiating measured
 *        launch, post-launch, AP wakeup, etc.
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

/*
 * NOTE: (TODO?) Stripped a lot of LCP, sleep, and MP code out of
 * tboot's version of this file.  Likely some of these are features
 * that we would like to have.  Look there instead of reinventing the
 * wheel when the time comes.
 */

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfhw.h>
#include <xmhf-debug.h>

#include "_txt_hash.h"
#include "_txt_acmod.h"

#define MTRR_TYPE_MIXED         -1
#define MMIO_APIC_BASE          0xFEE00000
#define NR_MMIO_APIC_PAGES      1
#define NR_MMIO_IOAPIC_PAGES    1
#define NR_MMIO_PCICFG_PAGES    1

/* saved MTRR state or NULL if orig. MTRRs have not been changed */
static mtrr_state_t *g_saved_mtrrs = NULL;


/*
 * this must be done for each processor so that all have the same
 * memory types
 */
bool set_mtrrs_for_acmod(acm_hdr_t *hdr)
{
    uint32_t eflags;
    unsigned long cr0, cr4;

    /*
     * need to do some things before we start changing MTRRs
     *
     * since this will modify some of the MTRRs, they should be saved first
     * so that they can be restored once the AC mod is done
     */

    /* disable interrupts */
    eflags = read_eflags(CASM_NOPARAM);

    xmhfhw_cpu_disable_intr(CASM_NOPARAM);

    /* save CR0 then disable cache (CRO.CD=1, CR0.NW=0) */
    cr0 = read_cr0(CASM_NOPARAM);
    write_cr0((cr0 & ~CR0_NW) | CR0_CD);

    /* flush caches */
    wbinvd(CASM_NOPARAM);

    /* save CR4 and disable global pages (CR4.PGE=0) */
    cr4 = read_cr4(CASM_NOPARAM);
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
    wbinvd(CASM_NOPARAM);

    /* enable MTRRs */
    set_all_mtrrs(true);

    /* restore CR0 (cacheing) */
    write_cr0(cr0);

    /* restore CR4 (global pages) */
    write_cr4(cr4);

    /* enable interrupts */
    write_eflags(eflags);



    return true;
}


//extern SL_PARAMETER_BLOCK *slpb; /* Ugh; ugly global from init.c */

bool get_parameters(getsec_parameters_t *params);

/*
 * this is the structure whose addr we'll put in TXT heap
 * it needs to be within the MLE pages, so force it to the .text section
 */
static mle_hdr_t g_mle_hdr = {
    .uuid              =  MLE_HDR_UUID,
    .length            =  sizeof(mle_hdr_t),
    .version           =  MLE_HDR_VER,
    .entry_point       =  TEMPORARY_HARDCODED_MLE_ENTRYPOINT, // XXX TODO remove magic number
    .first_valid_page  =  0,
    ///XXX I thnk these should be phys addres
    .mle_start_off     =  0, /* In MLE address space as accessed via MLE page tables */
    .mle_end_off       =  TEMPORARY_HARDCODED_MLE_SIZE, // XXX TODO remove magic number
    .capabilities      =  { MLE_HDR_CAPS },
    .cmdline_start_off =  0,
    .cmdline_end_off   =  0
};

///XXX
static void print_file_info(void)
{
    _XDPRINTF_("file addresses:\n");
    _XDPRINTF_("\t &g_mle_hdr=%p\n", &g_mle_hdr);
}

static void print_mle_hdr(const mle_hdr_t *mle_hdr)
{
    _XDPRINTF_("MLE header:\n");
    _XDPRINTF_("\t uuid="); print_uuid(&mle_hdr->uuid); _XDPRINTF_("\n");
    _XDPRINTF_("\t length=%x\n", mle_hdr->length);
    _XDPRINTF_("\t version=%08x\n", mle_hdr->version);
    _XDPRINTF_("\t entry_point=%08x\n", mle_hdr->entry_point);
    _XDPRINTF_("\t first_valid_page=%08x\n", mle_hdr->first_valid_page);
    _XDPRINTF_("\t mle_start_off=%x\n", mle_hdr->mle_start_off);
    _XDPRINTF_("\t mle_end_off=%x\n", mle_hdr->mle_end_off);
    print_txt_caps("\t ", mle_hdr->capabilities);
}

#define MAKE_PDTE(addr)  (PAGE_ALIGN_4K((uint32_t)addr) | 0x01)

/* we assume/know that our image is <2MB and thus fits w/in a single */
/* PT (512*4KB = 2MB) and thus fixed to 1 pg dir ptr and 1 pgdir and */
/* 1 ptable = 3 pages and just 1 loop loop for ptable MLE page table */
/* can only contain 4k pages */
static void *build_mle_pagetable(uint32_t mle_start, uint32_t mle_size)
{
    void *ptab_base;
    uint32_t ptab_size, mle_off;
    void *pg_dir_ptr_tab, *pg_dir, *pg_tab;
    uint64_t *pte;

    _XDPRINTF_("MLE start=%x, end=%x, size=%x\n", mle_start, mle_start+mle_size,
           mle_size);
    if ( mle_size > 512*PAGE_SIZE_4K ) {
        _XDPRINTF_("MLE size too big for single page table\n");
        return NULL;
    }

    /* should start on page boundary */
    if ( PAGE_ALIGN_4K(mle_start) != mle_start ) {
        _XDPRINTF_("MLE start is not page-aligned\n");
        return NULL;
    }

    /* place ptab_base below MLE */
    ptab_size = 3 * PAGE_SIZE_4K;      /* pgdir ptr + pgdir + ptab = 3 */
    ptab_base = (void *)(mle_start - ptab_size);

    /* NB: This memset will clobber the AMD-specific SL header.  That
     * is okay, as we are launching on an Intel TXT system. */
    memset(ptab_base, 0, ptab_size);
    _XDPRINTF_("ptab_size=%x, ptab_base=%p\n", ptab_size, ptab_base);

    pg_dir_ptr_tab = (void *)ptab_base;
    pg_dir         = (void *)((uint32_t)pg_dir_ptr_tab + PAGE_SIZE_4K);
    pg_tab         = (void *)((uint32_t)pg_dir + PAGE_SIZE_4K);

    /* only use first entry in page dir ptr table */
    *(uint64_t *)pg_dir_ptr_tab = MAKE_PDTE(pg_dir);

    _XDPRINTF_("*(uint64_t *)pg_dir_ptr_tab = 0x%16llx\n",
           *(uint64_t *)pg_dir_ptr_tab);

    /* only use first entry in page dir */
    *(uint64_t *)pg_dir = MAKE_PDTE(pg_tab);
    _XDPRINTF_("*(uint64_t *)pg_dir = 0x%16llx\n",
           *(uint64_t *)pg_dir);


    pte = pg_tab;
    mle_off = 0;
    do {
        *pte = MAKE_PDTE(mle_start + mle_off);
        _XDPRINTF_("pte = 0x%08x\n*pte = 0x%15llx\n",
               (uint32_t)pte, *pte);

        pte++;
        mle_off += PAGE_SIZE_4K;
    } while ( mle_off < mle_size );

    return ptab_base;
}

/*
 * will go through all modules to find an SINIT that matches the platform
 * (size can be NULL)
 */
static bool check_sinit_module(void *base, size_t size)
{
    txt_didvid_t didvid;
    txt_ver_fsbif_emif_t ver;

    if ( base == NULL )
        return false;

    /* display chipset fuse and device and vendor id info */
    unpack_txt_didvid_t(&didvid, read_pub_config_reg(TXTCR_DIDVID));
    _XDPRINTF_("chipset ids: vendor: 0x%x, device: 0x%x, revision: 0x%x\n",
           didvid.vendor_id, didvid.device_id, didvid.revision_id);
    unpack_txt_ver_fsbif_emif_t(&ver, read_pub_config_reg(TXTCR_VER_FSBIF));
    if ( (pack_txt_ver_fsbif_emif_t(&ver) & 0xffffffff) == 0xffffffff ||
         (pack_txt_ver_fsbif_emif_t(&ver) & 0xffffffff) == 0x00 )         /* need to use VER.EMIF */
        unpack_txt_ver_fsbif_emif_t(&ver, read_pub_config_reg(TXTCR_VER_EMIF));
    _XDPRINTF_("chipset production fused: %x\n", ver.prod_fused );

    if ( is_sinit_acmod(base, size, false) &&
         does_acmod_match_chipset((acm_hdr_t *)base) ) {
        _XDPRINTF_("SINIT matches platform\n");
        return true;
    }
    /* no SINIT found for this platform */
    _XDPRINTF_("no SINIT AC module found\n");
    return false;
}


/*
 * sets up TXT heap
 */
static txt_heap_t *init_txt_heap(void *ptab_base, acm_hdr_t *sinit,
                                 void *phys_mle_start, size_t mle_size)
{
    txt_heap_t *txt_heap;
    uint64_t *size;
    os_mle_data_t os_mle_data;
    os_sinit_data_t os_sinit_data;
    /* uint64_t min_lo_ram, max_lo_ram, min_hi_ram, max_hi_ram; */
    txt_caps_t sinit_caps;
    txt_caps_t caps_mask;

(void)mle_size;

    txt_heap = get_txt_heap();

    /*
     * BIOS data already setup by BIOS
     */
    if ( !verify_txt_heap(txt_heap, true) )
        return NULL;

    /*
     * OS/loader to MLE data
     */
    //os_mle_data =get_os_mle_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE));
    //size = (uint64_t *)((uint32_t)os_mle_data - sizeof(uint64_t));
    //*size = sizeof(*os_mle_data) + sizeof(uint64_t);
    //memset(os_mle_data, 0, sizeof(*os_mle_data));
    //os_mle_data->version = 0x02;
    //os_mle_data->mbi = NULL;
    //os_mle_data->saved_misc_enable_msr = rdmsr64(MSR_IA32_MISC_ENABLE);


	xmhfhw_sysmemaccess_writeu64(
		(get_os_mle_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)) - sizeof(uint64_t)),
		(uint32_t)(sizeof(os_mle_data) + sizeof(uint64_t)),
		(uint32_t)((uint64_t)(sizeof(os_mle_data) + sizeof(uint64_t)) >> 32) );

	    memset(&os_mle_data, 0, sizeof(os_mle_data));
	    os_mle_data.version = 0x02;
	    os_mle_data.mbi = NULL;
	    os_mle_data.saved_misc_enable_msr = rdmsr64(MSR_IA32_MISC_ENABLE);

	xmhfhw_sysmemaccess_copy(get_os_mle_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)),
			&os_mle_data, sizeof(os_mle_data_t));

	//_XDPRINTF_("Came %s:%u\n", __func__, __LINE__);
	//HALT();



    /*
     * OS/loader to SINIT data
     */

	//os_sinit_data = get_os_sinit_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE));
	//size = (uint64_t *)((uint32_t)os_sinit_data - sizeof(uint64_t));
	// *size = sizeof(*os_sinit_data) + sizeof(uint64_t);

	xmhfhw_sysmemaccess_writeu64(
		(get_os_sinit_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)) - sizeof(uint64_t)),
		(uint32_t)(sizeof(os_sinit_data) + sizeof(uint64_t)),
		(uint32_t)((uint64_t)(sizeof(os_sinit_data) + sizeof(uint64_t)) >> 32) );


	memset(&os_sinit_data, 0, sizeof(os_sinit_data));

	os_sinit_data.version = 5;
	os_sinit_data.mle_ptab = (uint64_t)(unsigned long)ptab_base;
	os_sinit_data.mle_size = g_mle_hdr.mle_end_off - g_mle_hdr.mle_start_off;

	HALT_ON_ERRORCOND(sizeof(mle_hdr_t) < TEMPORARY_MAX_MLE_HEADER_SIZE);
	memcpy(phys_mle_start, &g_mle_hdr, sizeof(mle_hdr_t));
	_XDPRINTF_("Copied mle_hdr (0x%08x, 0x%x bytes) into SL (0x%08x)\n",
	   (uint32_t)&g_mle_hdr, sizeof(mle_hdr_t), (uint32_t)phys_mle_start);

	os_sinit_data.mle_hdr_base = 0; // linear addr (offset from MLE base) of mle header, in MLE page tables


	os_sinit_data.vtd_pmr_lo_base = (uint64_t)__TARGET_BASE_SL;
	os_sinit_data.vtd_pmr_lo_size = (uint64_t)__TARGET_SIZE_SL;
	_XDPRINTF_("\nvtd_pmr_lo_base=%016llx, size=%016llx", os_sinit_data.vtd_pmr_lo_base, os_sinit_data.vtd_pmr_lo_size);

	sinit_caps = get_sinit_capabilities(sinit);
	caps_mask = 0;
	caps_mask = TXT_CAPS_T_RLP_WAKE_GETSEC | TXT_CAPS_T_RLP_WAKE_MONITOR;
	os_sinit_data.capabilities = MLE_HDR_CAPS & ~caps_mask;
	if ( sinit_caps & TXT_CAPS_T_RLP_WAKE_MONITOR )
		os_sinit_data.capabilities |= TXT_CAPS_T_RLP_WAKE_MONITOR;
	else if ( sinit_caps & TXT_CAPS_T_RLP_WAKE_GETSEC ){
		os_sinit_data.capabilities |= TXT_CAPS_T_RLP_WAKE_GETSEC;
	}else {     /* should have been detected in verify_acmod() */
		_XDPRINTF_("SINIT capabilities are icompatible (0x%x)\n", sinit_caps);
		return NULL;
	}

	os_sinit_data.capabilities &= ~(TXT_CAPS_T_ECX_PGTBL);

	print_os_sinit_data(&os_sinit_data);


	xmhfhw_sysmemaccess_copy(
		get_os_sinit_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)),
		&os_sinit_data,
		sizeof(os_sinit_data));





    /*
     * SINIT to MLE data will be setup by SINIT
     */

    return txt_heap;
}

void delay(uint64_t cycles)
{
    uint64_t start = rdtsc64(CASM_NOPARAM);

    while ( rdtsc64(CASM_NOPARAM)-start < cycles ) ;
}


tb_error_t txt_launch_environment(void *sinit_ptr, size_t sinit_size,
                                  void *phys_mle_start, size_t mle_size)
{
    acm_hdr_t *sinit;
    void *mle_ptab_base;
    os_mle_data_t os_mle_data;
    txt_heap_t *txt_heap;

    if(NULL == sinit_ptr) return TB_ERR_SINIT_NOT_PRESENT;
    else sinit = (acm_hdr_t*)sinit_ptr;

    if(!check_sinit_module((void *)sinit, sinit_size)) {
        _XDPRINTF_("check_sinit_module failed\n");
        return TB_ERR_SINIT_NOT_PRESENT;
    }
    /* if it is newer than BIOS-provided version, then copy it to */
    /* BIOS reserved region */
    sinit = copy_sinit(sinit);
    if ( sinit == NULL )
        return TB_ERR_SINIT_NOT_PRESENT;
    /* do some checks on it */
    if ( !verify_acmod(sinit) )
        return TB_ERR_ACMOD_VERIFY_FAILED;

    /* print some debug info */
    print_file_info();
    print_mle_hdr(&g_mle_hdr);

    /* create MLE page table */
    mle_ptab_base = build_mle_pagetable((uint32_t)phys_mle_start, mle_size);
    if ( mle_ptab_base == NULL )
        return TB_ERR_FATAL;

    /* initialize TXT heap */
    txt_heap = init_txt_heap(mle_ptab_base, sinit,
                             phys_mle_start, mle_size);
    if ( txt_heap == NULL )
        return TB_ERR_FATAL;

    /* save MTRRs before we alter them for SINIT launch */
    xmhfhw_sysmemaccess_copy(&os_mle_data, get_os_mle_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)),
				sizeof(os_mle_data_t));
    xmhfhw_cpu_x86_save_mtrrs(&(os_mle_data.saved_mtrr_state));
    xmhfhw_sysmemaccess_copy( get_os_mle_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)), &os_mle_data,
				sizeof(os_mle_data_t));

    /* set MTRRs properly for AC module (SINIT) */
    if ( !set_mtrrs_for_acmod(sinit) )
        return TB_ERR_FATAL;

    _XDPRINTF_("executing GETSEC[SENTER]...\n");
    /* pause before executing GETSEC[SENTER] */
    delay(0x80000000);

//#ifndef PERF_CRIT
//   if(NULL != slpb) {
//        __asm__ __volatile__ (
//            "cpuid\r\n"
//            "cpuid\r\n"
//            "cpuid\r\n"
//            "rdtsc\r\n"
//            : "=A"(slpb->rdtsc_before_drtm)
//            : /* no inputs */
//            : "ebx","ecx");
//    }
//#endif

    __getsec_senter((uint32_t)sinit, (sinit->size)*4);
    _XDPRINTF_("ERROR--we should not get here!\n");
    return TB_ERR_FATAL;
}


bool txt_prepare_cpu(void)
{
    uint32_t eflags, cr0;
    uint64_t mcg_cap, mcg_stat;
    getsec_parameters_t params;
    unsigned int i;

    /* must be running at CPL 0 => this is implicit in even getting this far */
    /* since our bootstrap code loads a GDT, etc. */
    cr0 = read_cr0(CASM_NOPARAM);

    /* must be in protected mode */
    if ( !(cr0 & CR0_PE) ) {
        _XDPRINTF_("ERR: not in protected mode\n");
        return false;
    }

    /* cache must be enabled (CR0.CD = CR0.NW = 0) */
    if ( cr0 & CR0_CD ) {
        _XDPRINTF_("CR0.CD set; clearing it.\n");
        cr0 &= ~CR0_CD;
    }
    if ( cr0 & CR0_NW ) {
        _XDPRINTF_("CR0.NW set; clearing it.\n");
        cr0 &= ~CR0_NW;
    }

    /* native FPU error reporting must be enabled for proper */
    /* interaction behavior */
    if ( !(cr0 & CR0_NE) ) {
        _XDPRINTF_("CR0.NE not set; setting it.\n");
        cr0 |= CR0_NE;
    }

    write_cr0(cr0);

    /* cannot be in virtual-8086 mode (EFLAGS.VM=1) */
    eflags = read_eflags(CASM_NOPARAM);

    if ( eflags & EFLAGS_VM ) {
        _XDPRINTF_("EFLAGS.VM set; clearing it.\n");
        write_eflags(eflags | ~EFLAGS_VM);

    }

    _XDPRINTF_("CR0 and EFLAGS OK\n");

    /*
     * verify that we're not already in a protected environment
     */
    if ( txt_is_launched() ) {
        _XDPRINTF_("already in protected environment\n");
        return false;
    }

    /*
     * verify all machine check status registers are clear (unless
     * support preserving them)
     */

    /* no machine check in progress (IA32_MCG_STATUS.MCIP=1) */
    mcg_stat = rdmsr64(MSR_MCG_STATUS);
    if ( mcg_stat & 0x04 ) {
        _XDPRINTF_("machine check in progress\n");
        return false;
    }

    if ( !get_parameters(&params) ) {
        _XDPRINTF_("get_parameters() failed\n");
        return false;
    }

    /* check if all machine check regs are clear */
    mcg_cap = rdmsr64(MSR_MCG_CAP);
    for ( i = 0; i < (mcg_cap & 0xff); i++ ) {
        mcg_stat = rdmsr64(MSR_MC0_STATUS + 4*i);
        if ( mcg_stat & (1ULL << 63) ) {
            _XDPRINTF_("MCG[%u] = %llx ERROR\n", i, mcg_stat);
            if ( !params.preserve_mce )
                return false;
        }
    }

    if ( params.preserve_mce )
        _XDPRINTF_("supports preserving machine check errors\n");
    else
        _XDPRINTF_("no machine check errors\n");

    if ( params.proc_based_scrtm )
        _XDPRINTF_("CPU support processor-based S-CRTM\n");

    /* all is well with the processor state */
    _XDPRINTF_("CPU is ready for SENTER\n");

    return true;
}



#define ACM_MEM_TYPE_UC                 0x0100
#define ACM_MEM_TYPE_WC                 0x0200
#define ACM_MEM_TYPE_WT                 0x1000
#define ACM_MEM_TYPE_WP                 0x2000
#define ACM_MEM_TYPE_WB                 0x4000

#define DEF_ACM_MAX_SIZE                0x8000
#define DEF_ACM_VER_MASK                0xffffffff
#define DEF_ACM_VER_SUPPORTED           0x00
#define DEF_ACM_MEM_TYPES               ACM_MEM_TYPE_UC
#define DEF_SENTER_CTRLS                0x00

bool get_parameters(getsec_parameters_t *params)
{
    unsigned long cr4;
    uint32_t index, eax, ebx, ecx;
    int param_type;

    /* sanity check because GETSEC[PARAMETERS] will fail if not set */
    cr4 = read_cr4(CASM_NOPARAM);
    if ( !(cr4 & CR4_SMXE) ) {
        _XDPRINTF_("SMXE not enabled, can't read parameters\n");
        return false;
    }

    memset(params, 0, sizeof(*params));
    params->acm_max_size = DEF_ACM_MAX_SIZE;
    params->acm_mem_types = DEF_ACM_MEM_TYPES;
    params->senter_controls = DEF_SENTER_CTRLS;
    params->proc_based_scrtm = false;
    params->preserve_mce = false;

    index = 0;
    do {
        __getsec_parameters(index++, &param_type, &eax, &ebx, &ecx);
        /* the code generated for a 'switch' statement doesn't work in this */
        /* environment, so use if/else blocks instead */

        /* NULL - all reserved */
        if ( param_type == 0 )
            ;
        /* supported ACM versions */
        else if ( param_type == 1 ) {
            if ( params->n_versions == MAX_SUPPORTED_ACM_VERSIONS )
                _XDPRINTF_("number of supported ACM version exceeds "
                       "MAX_SUPPORTED_ACM_VERSIONS\n");
            else {
                params->acm_versions[params->n_versions].mask = ebx;
                params->acm_versions[params->n_versions].version = ecx;
                params->n_versions++;
            }
        }
        /* max size AC execution area */
        else if ( param_type == 2 )
            params->acm_max_size = eax & 0xffffffe0;
        /* supported non-AC mem types */
        else if ( param_type == 3 )
            params->acm_mem_types = eax & 0xffffffe0;
        /* SENTER controls */
        else if ( param_type == 4 )
            params->senter_controls = (eax & 0x00007fff) >> 8;
        /* TXT extensions support */
        else if ( param_type == 5 ) {
            params->proc_based_scrtm = (eax & 0x00000020) ? true : false;
            params->preserve_mce = (eax & 0x00000040) ? true : false;
        }
        else {
            _XDPRINTF_("unknown GETSEC[PARAMETERS] type: %d\n", param_type);
            param_type = 0;    /* set so that we break out of the loop */
        }
    } while ( param_type != 0 );

    if ( params->n_versions == 0 ) {
        params->acm_versions[0].mask = DEF_ACM_VER_MASK;
        params->acm_versions[0].version = DEF_ACM_VER_SUPPORTED;
        params->n_versions = 1;
    }

    return true;
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
