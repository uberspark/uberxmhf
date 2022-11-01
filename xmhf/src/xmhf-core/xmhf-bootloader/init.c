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

//init.c - EMHF early initialization blob functionality
//author: amit vasudevan (amitvasudevan@acm.org)

//---includes-------------------------------------------------------------------
#include <xmhf.h>


//---forward prototypes---------------------------------------------------------
u32 smp_getinfo(PCPU *pcpus, u32 *num_pcpus);
void cstartup(multiboot_info_t *mbi);
MPFP * MP_GetFPStructure(void);
u32 _MPFPComputeChecksum(u32 spaddr, u32 size);
u32 isbsp(void);

//---globals--------------------------------------------------------------------
PCPU pcpus[MAX_PCPU_ENTRIES];
u32 pcpus_numentries=0;
u32 cpu_vendor;    //CPU_VENDOR_INTEL or CPU_VENDOR_AMD
u32 hypervisor_image_baseaddress;    //2M aligned highest physical memory address
//where the hypervisor binary is relocated to
GRUBE820 grube820list[MAX_E820_ENTRIES];
u32 grube820list_numentries=0;        //actual number of e820 entries returned
//by grub

//master-id table which holds LAPIC ID to VCPU mapping for each physical core
MIDTAB midtable[MAX_MIDTAB_ENTRIES] __attribute__(( section(".data") ));

//number of physical cores in the system
u32 midtable_numentries=0;

//VCPU buffers for all cores
VCPU vcpubuffers[MAX_VCPU_ENTRIES] __attribute__(( section(".data") ));

//initial stacks for all cores
u8 cpustacks[RUNTIME_STACK_SIZE * MAX_PCPU_ENTRIES] __attribute__(( section(".stack") ));

SL_PARAMETER_BLOCK *slpb = NULL;

#ifdef __DRT__
/* TODO: refactor to eliminate a lot of these globals, or at least use
 * static where appropriate */
static u8 *g_sinit_module_ptr = NULL;
static u32 g_sinit_module_size = 0;
#endif /* __DRT__ */

extern void init_core_lowlevel_setup(void);

/* Don't break the build if the Makefile fails to define these. */
#ifndef ___RUNTIME_INTEGRITY_HASH___
#define ___RUNTIME_INTEGRITY_HASH___ BAD_INTEGRITY_HASH
#endif /*  ___RUNTIME_INTEGRITY_HASH___ */
#ifndef ___SLABOVE64K_INTEGRITY_HASH___
#define ___SLABOVE64K_INTEGRITY_HASH___ BAD_INTEGRITY_HASH
#endif /*  ___SLABOVE64K_INTEGRITY_HASH___ */
#ifndef ___SLBELOW64K_INTEGRITY_HASH___
#define ___SLBELOW64K_INTEGRITY_HASH___ BAD_INTEGRITY_HASH
#endif /*  ___SLBELOW64K_INTEGRITY_HASH___ */

// we should get all of these from the build process, but don't forget
// that here in 'init' these values are UNTRUSTED
INTEGRITY_MEASUREMENT_VALUES g_init_gold /* __attribute__(( section("") )) */ = {
    .sha_runtime = ___RUNTIME_INTEGRITY_HASH___,
    .sha_slabove64K = ___SLABOVE64K_INTEGRITY_HASH___,
    .sha_slbelow64K = ___SLBELOW64K_INTEGRITY_HASH___
};

//size of SL + runtime in bytes
size_t sl_rt_size;


//---MP config table handling---------------------------------------------------
void dealwithMP(void){
    if(!smp_getinfo(pcpus, &pcpus_numentries)){
        printf("Fatal error with SMP detection. Halting!\n");
        HALT();
    }
}

//---INIT IPI routine-----------------------------------------------------------
void send_init_ipi_to_all_APs(void) {
    u32 eax, edx;
    volatile u32 *icr;
    u32 timeout = 0x01000000;

    //read LAPIC base address from MSR
    rdmsr(MSR_APIC_BASE, &eax, &edx);
    HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G
    printf("LAPIC base and status=0x%08x\n", eax);

    icr = (u32 *) (((u32)eax & 0xFFFFF000UL) + 0x300);

    //send INIT
    printf("Sending INIT IPI to all APs...\n");
    *icr = 0x000c4500UL;
    xmhf_baseplatform_arch_x86_udelay(10000);
    //wait for command completion
    while (--timeout > 0 && ((*icr) & 0x00001000U)) {
        xmhf_cpu_relax();
    }
    if(timeout == 0) {
        printf("\nERROR: send_init_ipi_to_all_APs() TIMEOUT!\n");
    }
    printf("\nDone.\n");
}



//---E820 parsing and handling--------------------------------------------------
//runtimesize is assumed to be 2M aligned
u32 dealwithE820(multiboot_info_t *mbi, u32 runtimesize __attribute__((unused))){
    //check if GRUB has a valid E820 map
    if(!(mbi->flags & MBI_MEMMAP)){
        printf("%s: no E820 map provided. HALT!\n", __FUNCTION__);
        HALT();
    }

    //zero out grub e820 list
    memset((void *)&grube820list, 0, sizeof(GRUBE820)*MAX_E820_ENTRIES);

    //grab e820 list into grube820list
    {
        // TODO: grube820list_numentries < MAX_E820_ENTRIES not checked.
        // Possible buffer overflow?
        memory_map_t *mmap;
        for ( mmap = (memory_map_t *) mbi->mmap_addr;
              (unsigned long) mmap < mbi->mmap_addr + mbi->mmap_length;
              mmap = (memory_map_t *) ((unsigned long) mmap
                                       + mmap->size + sizeof (mmap->size))){
            grube820list[grube820list_numentries].baseaddr_low = mmap->base_addr_low;
            grube820list[grube820list_numentries].baseaddr_high = mmap->base_addr_high;
            grube820list[grube820list_numentries].length_low = mmap->length_low;
            grube820list[grube820list_numentries].length_high = mmap->length_high;
            grube820list[grube820list_numentries].type = mmap->type;
            grube820list_numentries++;
        }
    }

    //debug: print grube820list
    {
        u32 i;
        printf("\noriginal system E820 map follows:\n");
        for(i=0; i < grube820list_numentries; i++){
            printf("0x%08x%08x, size=0x%08x%08x (%u)\n",
                   grube820list[i].baseaddr_high, grube820list[i].baseaddr_low,
                   grube820list[i].length_high, grube820list[i].length_low,
                   grube820list[i].type);
        }

    }

    //traverse e820 list forward to find an entry with type=0x1 (free)
    //with free amount of memory for runtime
    {
        u32 foundentry=0;
        u32 slruntimephysicalbase=__TARGET_BASE_SL;	//SL + runtime base
        u32 i;

        //for(i= (int)(grube820list_numentries-1); i >=0; i--){
		for(i= 0; i < grube820list_numentries; i++){
            u32 baseaddr, size;
            baseaddr = grube820list[i].baseaddr_low;
            size = grube820list[i].length_low;

            if(grube820list[i].type == 0x1){ //free memory?
                if(grube820list[i].baseaddr_high) //greater than 4GB? then skip
                    continue;

                if(grube820list[i].length_high){
                    printf("%s: E820 parsing error (64-bit length for < 4GB). HALT!\n");
                    HALT();
                }

			 	//check if this E820 range can accomodate SL + runtime
			 	if( slruntimephysicalbase >= baseaddr && (slruntimephysicalbase + runtimesize) < (baseaddr + size) ){
                    foundentry=1;
                    break;
                }
            }
        }

        if(!foundentry){
            printf("%s: unable to find E820 memory for SL+runtime. HALT!\n");
            HALT();
        }

		//entry number we need to split is indexed by i
		printf("proceeding to revise E820...\n");

		{

				//temporary E820 table with index
				GRUBE820 te820[MAX_E820_ENTRIES];
				u32 j=0;

				//copy all entries from original E820 table until index i
				for(j=0; j < i; j++)
					memcpy((void *)&te820[j], (void *)&grube820list[j], sizeof(GRUBE820));

				//we need a maximum of 2 extra entries for the final table, make a sanity check
				HALT_ON_ERRORCOND( (grube820list_numentries+2) < MAX_E820_ENTRIES );

				//split entry i into required number of entries depending on the memory range alignments
				if( (slruntimephysicalbase == grube820list[i].baseaddr_low) && ((slruntimephysicalbase+runtimesize) == (grube820list[i].baseaddr_low+grube820list[i].length_low)) ){
						//exact match, no split
						te820[j].baseaddr_high=0; te820[j].length_high=0; te820[j].baseaddr_low=grube820list[i].baseaddr_low; te820[j].length_low=grube820list[i].length_low; te820[j].type=grube820list[i].type;
						j++;
						i++;
				}else if ( (slruntimephysicalbase == grube820list[i].baseaddr_low) && (runtimesize < grube820list[i].length_low) ){
						//left aligned, split into 2
						te820[j].baseaddr_high=0; te820[j].length_high=0; te820[j].baseaddr_low=grube820list[i].baseaddr_low; te820[j].length_low=runtimesize; te820[j].type=0x2;
						j++;
						te820[j].baseaddr_high=0; te820[j].length_high=0; te820[j].baseaddr_low=grube820list[i].baseaddr_low+runtimesize; te820[j].length_low=grube820list[i].length_low-runtimesize; te820[j].type=1;
						j++;
						i++;
				}else if ( ((slruntimephysicalbase+runtimesize) == (grube820list[i].baseaddr_low+grube820list[i].length_low)) && slruntimephysicalbase > grube820list[i].baseaddr_low ){
						//right aligned, split into 2
						te820[j].baseaddr_high=0; te820[j].length_high=0; te820[j].baseaddr_low=grube820list[i].baseaddr_low; te820[j].length_low=slruntimephysicalbase-grube820list[i].baseaddr_low; te820[j].type=0x1;
						j++;
						te820[j].baseaddr_high=0; te820[j].length_high=0; te820[j].baseaddr_low= slruntimephysicalbase; te820[j].length_low=runtimesize; te820[j].type=0x1;
						j++;
						i++;
				}else{
						//range in the middle, split into 3
						te820[j].baseaddr_high=0; te820[j].length_high=0; te820[j].baseaddr_low=grube820list[i].baseaddr_low; te820[j].length_low=slruntimephysicalbase-grube820list[i].baseaddr_low; te820[j].type=0x1;
						j++;
						te820[j].baseaddr_high=0; te820[j].length_high=0; te820[j].baseaddr_low=slruntimephysicalbase; te820[j].length_low=runtimesize; te820[j].type=0x2;
						j++;
						te820[j].baseaddr_high=0; te820[j].length_high=0; te820[j].baseaddr_low=slruntimephysicalbase+runtimesize; te820[j].length_low=grube820list[i].length_low-runtimesize-(slruntimephysicalbase-grube820list[i].baseaddr_low); te820[j].type=1;
						j++;
						i++;
				}

				//copy entries i through end of original E820 list into temporary E820 list starting at index j
				while(i < grube820list_numentries){
					memcpy((void *)&te820[j], (void *)&grube820list[i], sizeof(GRUBE820));
					i++;
					j++;
				}

				//copy temporary E820 list into global E20 list and setup final E820 entry count
				grube820list_numentries = j;
				memcpy((void *)&grube820list, (void *)&te820, (grube820list_numentries * sizeof(GRUBE820)) );
		}

		printf("E820 revision complete.\n");

		//debug: print grube820list
		{
			u32 i;
			printf("\nrevised system E820 map follows:\n");
			for(i=0; i < grube820list_numentries; i++){
				printf("0x%08x%08x, size=0x%08x%08x (%u)\n",
					   grube820list[i].baseaddr_high, grube820list[i].baseaddr_low,
					   grube820list[i].length_high, grube820list[i].length_low,
					   grube820list[i].type);
			}
		}


        return slruntimephysicalbase;
    }

}

#ifdef __DRT__

/*
 * XMHF: The following symbols are taken from tboot-1.10.5
 * Changes made include:
 *  Change return type of __getsec_capabilities() to uint32_t.
 *  TODO: assuming vtd_bios_enabled() is true
 *  TODO: verify_IA32_se_svn_status() skipped
 *  TODO: get_tboot_call_racm() skipped
 * List of major symbols:
 *  read_processor_info
 *  supports_vmx
 *  supports_smx
 *  use_mwait
 *  supports_txt
 *  txt_verify_platform
 *  txt_has_error
 *  txt_display_errors
 *  txt_do_senter
 */

#define X86_EFLAGS_ID EFLAGS_ID
#define do_cpuid(a, p) cpuid(a, &p[0], &p[1], &p[2], &p[3])
#define get_tboot_mwait() (false)
#define CPUID_X86_FEATURE_XMM3   (1<<0)
#define MSR_IA32_MISC_ENABLE_MONITOR_FSM       (1<<18)
#define __getsec_capabilities(index) \
({ \
    uint32_t cap; \
    __asm__ __volatile__ (IA32_GETSEC_OPCODE "\n" \
              : "=a"(cap) \
              : "a"(IA32_GETSEC_CAPABILITIES), "b"(index)); \
    cap; \
})

/*
 * CPUID extended feature info
 */
static unsigned int g_cpuid_ext_feat_info;

/*
 * IA32_FEATURE_CONTROL_MSR
 */
static unsigned long g_feat_ctrl_msr;


static bool read_processor_info(void)
{
    unsigned long f1, f2;
     /* eax: regs[0], ebx: regs[1], ecx: regs[2], edx: regs[3] */
    uint32_t regs[4];

    /* is CPUID supported? */
    /* (it's supported if ID flag in EFLAGS can be set and cleared) */
    asm("pushf\n\t"
        "pushf\n\t"
        "pop %0\n\t"
        "mov %0,%1\n\t"
        "xor %2,%0\n\t"
        "push %0\n\t"
        "popf\n\t"
        "pushf\n\t"
        "pop %0\n\t"
        "popf\n\t"
        : "=&r" (f1), "=&r" (f2)
        : "ir" (X86_EFLAGS_ID));
    if ( ((f1^f2) & X86_EFLAGS_ID) == 0 ) {
        g_cpuid_ext_feat_info = 0;
        printf("CPUID instruction is not supported.\n");
        return false;
    }

    do_cpuid(0, regs);
    if ( regs[1] != 0x756e6547        /* "Genu" */
         || regs[2] != 0x6c65746e     /* "ntel" */
         || regs[3] != 0x49656e69 ) { /* "ineI" */
        g_cpuid_ext_feat_info = 0;
        printf("Non-Intel CPU detected.\n");
        return false;
    }
    g_cpuid_ext_feat_info = cpuid_ecx(1);

    /* read feature control msr only if processor supports VMX or SMX instructions */
    if ( (g_cpuid_ext_feat_info & CPUID_X86_FEATURE_VMX) ||
         (g_cpuid_ext_feat_info & CPUID_X86_FEATURE_SMX) ) {
        g_feat_ctrl_msr = rdmsr64(MSR_IA32_FEATURE_CONTROL);
        printf("IA32_FEATURE_CONTROL_MSR: %08lx\n", g_feat_ctrl_msr);
    }

    return true;
}

static bool supports_vmx(void)
{
    /* check that processor supports VMX instructions */
    if ( !(g_cpuid_ext_feat_info & CPUID_X86_FEATURE_VMX) ) {
        printf("ERR: CPU does not support VMX\n");
        return false;
    }
    printf("CPU is VMX-capable\n");

    /* and that VMX is enabled in the feature control MSR */
    if ( !(g_feat_ctrl_msr & IA32_FEATURE_CONTROL_MSR_ENABLE_VMX_IN_SMX) ) {
        printf("ERR: VMXON disabled by feature control MSR (%lx)\n",
               g_feat_ctrl_msr);
        return false;
    }

    return true;
}

static bool supports_smx(void)
{
    /* check that processor supports SMX instructions */
    if ( !(g_cpuid_ext_feat_info & CPUID_X86_FEATURE_SMX) ) {
        printf("ERR: CPU does not support SMX\n");
        return false;
    }
    printf("CPU is SMX-capable\n");

    /*
     * and that SMX is enabled in the feature control MSR
     */

    /* check that the MSR is locked -- BIOS should always lock it */
    if ( !(g_feat_ctrl_msr & IA32_FEATURE_CONTROL_MSR_LOCK) ) {
        printf("ERR: IA32_FEATURE_CONTROL_MSR_LOCK is not locked\n");
        /* this should not happen, as BIOS is required to lock the MSR */
#ifdef PERMISSIVE_BOOT
        /* we enable VMX outside of SMX as well so that if there was some */
        /* error in the TXT boot, VMX will continue to work */
        g_feat_ctrl_msr |= IA32_FEATURE_CONTROL_MSR_ENABLE_VMX_IN_SMX |
                           IA32_FEATURE_CONTROL_MSR_ENABLE_VMX_OUT_SMX |
                           IA32_FEATURE_CONTROL_MSR_ENABLE_SENTER |
                           IA32_FEATURE_CONTROL_MSR_SENTER_PARAM_CTL |
                           IA32_FEATURE_CONTROL_MSR_LOCK;
        wrmsrl(MSR_IA32_FEATURE_CONTROL, g_feat_ctrl_msr);
        return true;
#else
        return false;
#endif
    }

    /* check that SENTER (w/ full params) is enabled */
    if ( !(g_feat_ctrl_msr & (IA32_FEATURE_CONTROL_MSR_ENABLE_SENTER |
                              IA32_FEATURE_CONTROL_MSR_SENTER_PARAM_CTL)) ) {
        printf("ERR: SENTER disabled by feature control MSR (%lx)\n",
               g_feat_ctrl_msr);
        return false;
    }

    return true;
}

bool use_mwait(void)
{
    return get_tboot_mwait() && (g_cpuid_ext_feat_info & CPUID_X86_FEATURE_XMM3);
}

tb_error_t supports_txt(void)
{
    capabilities_t cap;

    /* processor must support cpuid and must be Intel CPU */
    if ( !read_processor_info() )
        return TB_ERR_SMX_NOT_SUPPORTED;

    /* processor must support SMX */
    if ( !supports_smx() )
        return TB_ERR_SMX_NOT_SUPPORTED;

    if ( use_mwait() ) {
        /* set MONITOR/MWAIT support (SENTER will clear, so always set) */
        uint64_t misc;
        misc = rdmsr64(MSR_IA32_MISC_ENABLE);
        misc |= MSR_IA32_MISC_ENABLE_MONITOR_FSM;
        wrmsr64(MSR_IA32_MISC_ENABLE, misc);
    }
    else if ( !supports_vmx() ) {
        return TB_ERR_VMX_NOT_SUPPORTED;
    }

    /* testing for chipset support requires enabling SMX on the processor */
    write_cr4(read_cr4() | CR4_SMXE);
    printf("SMX is enabled\n");

    /*
     * verify that an TXT-capable chipset is present and
     * check that all needed SMX capabilities are supported
     */

    // XMHF: Change return type of __getsec_capabilities() to uint32_t.
    cap = (capabilities_t)__getsec_capabilities(0);
    if ( cap.chipset_present ) {
        if ( cap.senter && cap.sexit && cap.parameters && cap.smctrl &&
             cap.wakeup ) {
            printf("TXT chipset and all needed capabilities present\n");
            return TB_ERR_NONE;
        }
        else
            printf("ERR: insufficient SMX capabilities (%x)\n", cap._raw);
    }
    else
        printf("ERR: TXT-capable chipset not present\n");

    /* since we are failing, we should clear the SMX flag */
    write_cr4(read_cr4() & ~CR4_SMXE);

    return TB_ERR_TXT_NOT_SUPPORTED;
}

tb_error_t txt_verify_platform(void)
{
    txt_heap_t *txt_heap;
    tb_error_t err;
    txt_ests_t ests;

    /* check TXT supported */
    err = supports_txt();
    if ( err != TB_ERR_NONE )
        return err;

    // XMHF: TODO: assuming vtd_bios_enabled() is true
    //if ( !vtd_bios_enabled() ) {
    //    return TB_ERR_VTD_NOT_SUPPORTED;
    //}

    /* check is TXT_RESET.STS is set, since if it is SENTER will fail */
    ests = (txt_ests_t)read_pub_config_reg(TXTCR_ESTS);
    if ( ests.txt_reset_sts ) {
        printf("TXT_RESET.STS is set and SENTER is disabled (0x%02llx)\n",
               ests._raw);
        return TB_ERR_SMX_NOT_SUPPORTED;
    }

    /* verify BIOS to OS data */
    txt_heap = get_txt_heap();
    if ( !verify_bios_data(txt_heap) )
        return TB_ERR_TXT_NOT_SUPPORTED;

    return TB_ERR_NONE;
}

bool txt_has_error(void)
{
    txt_errorcode_t err;

    err = (txt_errorcode_t)read_pub_config_reg(TXTCR_ERRORCODE);
    if (err._raw == 0 || err._raw == 0xc0000001 || err._raw == 0xc0000009) {
        return false;
    }
    else {
        return true;
    }
}

/* Read values in TXT status registers */
void txt_display_errors(void)
{
    txt_errorcode_t err;
    txt_ests_t ests;
    txt_e2sts_t e2sts;
    txt_errorcode_sw_t sw_err;
    acmod_error_t acmod_err;

    /*
     * display TXT.ERRORODE error
     */
    err = (txt_errorcode_t)read_pub_config_reg(TXTCR_ERRORCODE);
    if (txt_has_error() == false)
        printf("TXT.ERRORCODE: 0x%llx\n", err._raw);
    else
        printf("TXT.ERRORCODE: 0x%llx\n", err._raw);

    /* AC module error (don't know how to parse other errors) */
    if ( err.valid ) {
        if ( err.external == 0 )       /* processor error */
            printf("\t processor error 0x%x\n", (uint32_t)err.type);
        else {                         /* external SW error */
            sw_err._raw = err.type;
            if ( sw_err.src == 1 )     /* unknown SW error */
                printf("unknown SW error 0x%x:0x%x\n", sw_err.err1, sw_err.err2);
            else {                     /* ACM error */
                acmod_err._raw = sw_err._raw;
                if ( acmod_err._raw == 0x0 || acmod_err._raw == 0x1 ||
                     acmod_err._raw == 0x9 )
                    printf("AC module error : acm_type=0x%x, progress=0x%02x, "
                           "error=0x%x\n", acmod_err.acm_type, acmod_err.progress,
                           acmod_err.error);
                else
                    printf("AC module error : acm_type=0x%x, progress=0x%02x, "
                           "error=0x%x\n", acmod_err.acm_type, acmod_err.progress,
                           acmod_err.error);
                /* error = 0x0a, progress = 0x0d => TPM error */
                if ( acmod_err.error == 0x0a && acmod_err.progress == 0x0d )
                    printf("TPM error code = 0x%x\n", acmod_err.tpm_err);
                /* progress = 0x10 => LCP2 error */
                else if ( acmod_err.progress == 0x10 && acmod_err.lcp_minor != 0 )
                    printf("LCP2 error:  minor error = 0x%x, index = %u\n",
                           acmod_err.lcp_minor, acmod_err.lcp_index);
            }
        }
    }

    /*
     * display TXT.ESTS error
     */
    ests = (txt_ests_t)read_pub_config_reg(TXTCR_ESTS);
    if (ests._raw == 0)
        printf("TXT.ESTS: 0x%llx\n", ests._raw);
    else
        printf("TXT.ESTS: 0x%llx\n", ests._raw);

    /*
     * display TXT.E2STS error
     */
    e2sts = (txt_e2sts_t)read_pub_config_reg(TXTCR_E2STS);
    if (e2sts._raw == 0 || e2sts._raw == 0x200000000)
        printf("TXT.E2STS: 0x%llx\n", e2sts._raw);
    else
        printf("TXT.E2STS: 0x%llx\n", e2sts._raw);
}

/* Transfer control to the SL using GETSEC[SENTER] */
/*///XXX TODO not fully functional yet. Expected flow:
txt_prepare_cpu();
txt_verify_platform();
// Legacy USB?
    // disable legacy USB #SMIs
    get_tboot_no_usb();
    disable_smis();
prepare_tpm();
txt_launch_environment(mbi);*/

bool txt_do_senter(void *phys_mle_start, size_t mle_size) {
    tb_error_t err;

    if (!tpm_detect()) {
        printf("ERROR: tpm_detect() failed\n");
        return false;
    }

    // XMHF: TODO: verify_IA32_se_svn_status() skipped
    // XMHF: TODO: get_tboot_call_racm() skipped
    
    if (supports_txt() != TB_ERR_NONE) {
        printf("ERROR: supports_txt() failed\n");
        return false;
    }

    txt_display_errors();

    if((err = txt_verify_platform()) != TB_ERR_NONE) {
        printf("ERROR: txt_verify_platform returned 0x%08x\n", (u32)err);
        return false;
    }
    if(!txt_prepare_cpu()) {
        printf("ERROR: txt_prepare_cpu failed.\n");
        return false;
    }

    if (!prepare_tpm()) {
        printf("ERROR: prepare_tpm() failed.\n");
        return false;
    }

    ///XXX TODO get addresses of SL, populate a mle_hdr_t
    txt_launch_environment(g_sinit_module_ptr, g_sinit_module_size,
                           phys_mle_start, mle_size);

    return false; /* unreachable if launch is successful, thus should return failure */
}

/**
 * Check each module to see if it is an SINIT module.  If it is, set
 * the globals g_sinit_module_ptr and g_sinit_module_size to point to
 * it.
 *
 * Returns true if an SINIT module was found, false otherwise.
 */
static bool txt_parse_sinit(module_t *mod_array, unsigned int mods_count) {
    int i;
    unsigned int bytes;

    /* I can't think of a legitimate reason why this would ever be
     * this large. */
    if(mods_count > 10) {
        return false;
    }

    for(i=(int)mods_count-1; i >= 0; i--) {
        bytes = mod_array[i].mod_end - mod_array[i].mod_start;
        printf("\nChecking whether MBI module %i is SINIT...\n", i);
        if(is_sinit_acmod((void*)mod_array[i].mod_start, bytes, false)) {
            g_sinit_module_ptr = (u8*)mod_array[i].mod_start;
            g_sinit_module_size = bytes;
            printf("YES! SINIT found @ %p, %d bytes\n",
                   g_sinit_module_ptr, g_sinit_module_size);
            return true;
        } else {
            printf("no.\n");
        }
    }

    return false;
}

//---svm_verify_platform-------------------------------------------------------
//do some basic checks on SVM platform to ensure DRTM should work as expected
static bool svm_verify_platform(void) __attribute__((unused));
static bool svm_verify_platform(void)
{
    uint32_t eax, edx, ebx, ecx;
    uint64_t efer;

    cpuid(0x80000001, &eax, &ebx, &ecx, &edx);

    if ((ecx & SVM_CPUID_FEATURE) == 0) {
        printf("ERR: CPU does not support AMD SVM\n");
        return false;
    }

    /* Check whether SVM feature is disabled in BIOS */
    rdmsr(VM_CR_MSR, &eax, &edx);
    if (eax & VM_CR_SVME_DISABLE) {
        printf("ERR: AMD SVM Extension is disabled in BIOS\n");
        return false;
    }

    /* Turn on SVM */
    efer = rdmsr64(MSR_EFER);
    wrmsr64(MSR_EFER, efer | (1<<EFER_SVME));
    efer = rdmsr64(MSR_EFER);
    if ((efer & (1<<EFER_SVME)) == 0) {
        printf("ERR: Could not enable AMD SVM\n");
        return false;
    }

    cpuid(0x8000000A, &eax, &ebx, &ecx, &edx);
    printf("AMD SVM version %d enabled\n", eax & 0xff);

    return true;
}

//---svm_platform_checks--------------------------------------------------------
//attempt to detect if there is a platform issue that will prevent
//successful invocation of skinit
static bool svm_prepare_cpu(void)
{
    uint64_t mcg_cap, mcg_stat;
    uint64_t apicbase;
    uint32_t cr0;
    u32 i, bound;

    /* must be running at CPL 0 => this is implicit in even getting this far */
    /* since our bootstrap code loads a GDT, etc. */

    /* must be in protected mode */
    cr0 = read_cr0();
    if (!(cr0 & CR0_PE)) {
        printf("ERR: not in protected mode\n");
        return false;
    }

    /* make sure the APIC is enabled */
    apicbase = rdmsr64(MSR_APIC_BASE);
    if (!(apicbase & MSR_IA32_APICBASE_ENABLE)) {
        printf("APIC disabled\n");
        return false;
    }

    /* verify all machine check status registers are clear */

    /* no machine check in progress (IA32_MCG_STATUS.MCIP=1) */
    mcg_stat = rdmsr64(MSR_MCG_STATUS);
    if (mcg_stat & 0x04) {
        printf("machine check in progress\n");
        return false;
    }

    /* all machine check regs are clear */
    mcg_cap = rdmsr64(MSR_MCG_CAP);
    bound = (u32)mcg_cap & 0x000000ff;
    for (i = 0; i < bound; i++) {
        mcg_stat = rdmsr64(MSR_MC0_STATUS + 4*i);
        if (mcg_stat & (1ULL << 63)) {
            printf("MCG[%d] = %llx ERROR\n", i, mcg_stat);
            return false;
        }
    }

    printf("no machine check errors\n");

    /* clear microcode on all the APs handled in mp_cstartup() */
    /* put all APs in INIT handled in do_drtm() */

    /* all is well with the processor state */
    printf("CPU is ready for SKINIT\n");

    return true;
}
#endif /* __DRT__ */

//---do_drtm--------------------------------------------------------------------
//this establishes a dynamic root of trust
//inputs:
//cpu_vendor = intel or amd
//slbase= physical memory address of start of sl
void do_drtm(VCPU __attribute__((unused))*vcpu, u32 slbase, size_t mle_size __attribute__((unused))){
#ifdef __MP_VERSION__
    HALT_ON_ERRORCOND(vcpu->id == 0);
    //send INIT IPI to all APs
    send_init_ipi_to_all_APs();
    printf("INIT(early): sent INIT IPI to APs\n");
#endif

#if defined (__DRT__)

    if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
        if(!svm_verify_platform()) {
            printf("\nINIT(early): ERROR: svm_verify_platform FAILED!\n");
            HALT();
        }
        if(!svm_prepare_cpu()) {
            printf("\nINIT(early): ERROR: svm_prepare_cpu FAILED!\n");
            HALT();
        }
        //issue SKINIT
        //our secure loader is the first 64K of the hypervisor image
        printf("INIT(early): transferring control to SL via SKINIT...\n");
		#ifndef PERF_CRIT
        if(NULL != slpb) {
            slpb->rdtsc_before_drtm = rdtsc64();
        }
		#endif
        skinit((u32)slbase);
    } else {
        printf("\n******  INIT(early): Begin TXT Stuff  ******\n");
        txt_do_senter((void*)(slbase+3*PAGE_SIZE_4K), TEMPORARY_HARDCODED_MLE_SIZE);
        printf("INIT(early): error(fatal), should never come here!\n");
        HALT();
    }

#else  //!__DRT__
	//don't use SKINIT or SENTER
	{
		u32 sl_entry_point;
		u16 *sl_entry_point_offset = (u16 *)slbase;
		typedef void(*FCALL)(void);
		FCALL invokesl;

		printf("\n****** NO DRTM startup ******\n");
		printf("slbase=0x%08x, sl_entry_point_offset=0x%08x\n", (u32)slbase, *sl_entry_point_offset);
		sl_entry_point = (u32)slbase + (u32) (*sl_entry_point_offset);
		invokesl = (FCALL)(u32)sl_entry_point;
		printf("SL entry point to transfer control to: 0x%08x\n", invokesl);
		invokesl();
        printf("INIT(early): error(fatal), should never come here!\n");
        HALT();
	}
#endif

}


void setupvcpus(u32 cpu_vendor, MIDTAB *midtable, u32 midtable_numentries){
    u32 i;
    VCPU *vcpu;

    printf("%s: cpustacks range 0x%08x-0x%08x in 0x%08x chunks\n",
           __FUNCTION__, (u32)cpustacks, (u32)cpustacks + (RUNTIME_STACK_SIZE * MAX_VCPU_ENTRIES),
           RUNTIME_STACK_SIZE);
    printf("%s: vcpubuffers range 0x%08x-0x%08x in 0x%08x chunks\n",
           __FUNCTION__, (u32)vcpubuffers, (u32)vcpubuffers + (SIZE_STRUCT_VCPU * MAX_VCPU_ENTRIES),
           SIZE_STRUCT_VCPU);

    for(i=0; i < midtable_numentries; i++){
        vcpu = (VCPU *)((u32)vcpubuffers + (u32)(i * SIZE_STRUCT_VCPU));
        memset((void *)vcpu, 0, sizeof(VCPU));

        vcpu->cpu_vendor = cpu_vendor;

        vcpu->esp = ((u32)cpustacks + (i * RUNTIME_STACK_SIZE)) + RUNTIME_STACK_SIZE;
        vcpu->id = midtable[i].cpu_lapic_id;

        midtable[i].vcpu_vaddr_ptr = (u32)vcpu;
        printf("CPU #%u: vcpu_vaddr_ptr=0x%08x, esp=0x%08x\n", i, midtable[i].vcpu_vaddr_ptr,
               vcpu->esp);
    }
}


//---wakeupAPs------------------------------------------------------------------
void wakeupAPs(void){
    u32 eax, edx;
    volatile u32 *icr;

    //read LAPIC base address from MSR
    rdmsr(MSR_APIC_BASE, &eax, &edx);
    HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G
    //printf("LAPIC base and status=0x%08x\n", eax);

    icr = (u32 *) (((u32)eax & 0xFFFFF000UL) + 0x300);

    {
        extern u32 _ap_bootstrap_start[], _ap_bootstrap_end[];
        memcpy((void *)0x10000, (void *)_ap_bootstrap_start, (u32)_ap_bootstrap_end - (u32)_ap_bootstrap_start + 1);
    }

    //our test code is at 1000:0000, we need to send 10 as vector
    //send INIT
    printf("Sending INIT IPI to all APs...");
    *icr = 0x000c4500UL;
    xmhf_baseplatform_arch_x86_udelay(10000);
    //wait for command completion
    while ((*icr) & 0x1000U) {
        xmhf_cpu_relax();
    }
    printf("Done.\n");

    //send SIPI (twice as per the MP protocol)
    {
        int i;
        for(i=0; i < 2; i++){
            printf("Sending SIPI-%u...", i);
            *icr = 0x000c4610UL;
            xmhf_baseplatform_arch_x86_udelay(200);
            //wait for command completion
            while ((*icr) & 0x1000U) {
                xmhf_cpu_relax();
            }
            printf("Done.\n");
        }
    }

    printf("APs should be awake!\n");
}

/* The TPM must be ready for the AMD CPU to send it commands at
 * Locality 4 when executing SKINIT. Ideally all that is necessary is
 * to xmhf_tpm_deactivate_all_localities(), but some TPM's are still not
 * sufficiently "awake" after that.  Thus, make sure it successfully
 * responds to a command at some locality, *then*
 * xmhf_tpm_deactivate_all_localities().
 */
bool svm_prepare_tpm(void) {
    uint32_t locality = EMHF_TPM_LOCALITY_PREF; /* target.h */
    bool ret = true;

    printf("INIT:TPM: prepare_tpm starting.\n");
    //dump_locality_access_regs();
    xmhf_tpm_deactivate_all_localities();
    //dump_locality_access_regs();

    if(tpm_wait_cmd_ready(locality)) {
        printf("INIT:TPM: successfully opened in Locality %d.\n", locality);
    } else {
        printf("INIT:TPM: ERROR: Locality %d could not be opened.\n", locality);
        ret = false;
    }
    xmhf_tpm_deactivate_all_localities();
    //dump_locality_access_regs();
    printf("INIT:TPM: prepare_tpm done.\n");

    return ret;
}

//---init main----------------------------------------------------------------
void cstartup(multiboot_info_t *mbi){
    module_t *mod_array;
    u32 mods_count;

    /* parse command line */
    memset(g_cmdline, '\0', sizeof(g_cmdline));
    strncpy(g_cmdline, (char*)mbi->cmdline, sizeof(g_cmdline)-1);
    g_cmdline[sizeof(g_cmdline)-1] = '\0'; /* in case strncpy truncated */
    tboot_parse_cmdline();

#if defined (__DEBUG_SERIAL__)
    /* parse serial port params */
    {
      uart_config_t uart_config_backup = g_uart_config;
      if(!get_tboot_serial()) {
          /* TODO: What's going on here? Redundant? */
          g_uart_config = uart_config_backup;
      }
    }

    //initialize debugging early on
	xmhf_debug_init((char *)&g_uart_config);
#endif

    mod_array = (module_t*)mbi->mods_addr;
    mods_count = mbi->mods_count;

	//welcome banner
	printf("eXtensible Modular Hypervisor Framework (XMHF) %s\n", ___XMHF_BUILD_VERSION___);
	printf("Build revision: %s\n", ___XMHF_BUILD_REVISION___);
#ifdef __XMHF_AMD64__
	printf("Subarch: amd64\n\n");
#elif __XMHF_I386__
	printf("Subarch: i386\n\n");
#else /* !defined(__XMHF_I386__) && !defined(__XMHF_AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__XMHF_I386__) && !defined(__XMHF_AMD64__) */

    printf("INIT(early): initializing, total modules=%u\n", mods_count);

    //check CPU type (Intel vs AMD)
    cpu_vendor = get_cpu_vendor_or_die(); // HALT()'s if unrecognized

    if(CPU_VENDOR_INTEL == cpu_vendor) {
        printf("INIT(early): detected an Intel CPU\n");

#ifdef __DRT__
        /* Intel systems require an SINIT module */
        if(!txt_parse_sinit(mod_array, mods_count)) {
            printf("INIT(early): FATAL ERROR: Intel CPU without SINIT module!\n");
            HALT();
        }
#endif /* __DRT__ */
    } else if(CPU_VENDOR_AMD == cpu_vendor) {
        printf("INIT(early): detected an AMD CPU\n");
    } else {
        printf("INIT(early): Dazed and confused: Unknown CPU vendor %d\n", cpu_vendor);
    }

#ifdef __XMHF_AMD64__
    //check whether 64-bit is supported by the CPU
    {
        uint32_t eax, edx, ebx, ecx;
        cpuid(0x80000000U, &eax, &ebx, &ecx, &edx);
        HALT_ON_ERRORCOND(eax >= 0x80000001U);
        cpuid(0x80000001U, &eax, &ebx, &ecx, &edx);
        HALT_ON_ERRORCOND((edx & (1U << 29)) && "64-bit not supported");
    }
#elif !defined(__XMHF_I386__)
    #error "Unsupported Arch"
#endif /* !defined(__XMHF_I386__) */

    //deal with MP and get CPU table
    dealwithMP();

    //check number of elements in mod_array. Currently bootloader assumes that
    //mod_array[0] is SL+RT, mod_array[1] is guest OS boot module.
    HALT_ON_ERRORCOND(mods_count >= 2);

    //find highest 2MB aligned physical memory address that the hypervisor
    //binary must be moved to
    sl_rt_size = mod_array[0].mod_end - mod_array[0].mod_start;

#ifdef __SKIP_RUNTIME_BSS__
    {
        RPB *rpb = (RPB *) (mod_array[0].mod_start + 0x200000);
        sl_rt_size = PAGE_ALIGN_UP_2M((u32)rpb->XtVmmRuntimeBssEnd - __TARGET_BASE_SL);
    }
#endif /* __SKIP_RUNTIME_BSS__ */

    hypervisor_image_baseaddress = dealwithE820(mbi, PAGE_ALIGN_UP_2M((sl_rt_size)));

    //check whether multiboot modules overlap with SL+RT. mod_array[0] can
    //overlap because we will use memmove() instead of memcpy(). Currently
    //will panic if other mod_array[i] overlaps with SL+RT.
    {
        u32 i;
        u32 sl_rt_start = hypervisor_image_baseaddress;
        u32 sl_rt_end;
        HALT_ON_ERRORCOND(!plus_overflow_u32(sl_rt_start, sl_rt_size));
        sl_rt_end = sl_rt_start + sl_rt_size;
        for(i=1; i < mods_count; i++) {
			HALT_ON_ERRORCOND(mod_array[i].mod_start >= sl_rt_end ||
			                  sl_rt_start >= mod_array[i].mod_end);
        }
    }

    //relocate the hypervisor binary to the above calculated address
    memmove((void*)hypervisor_image_baseaddress, (void*)mod_array[0].mod_start, sl_rt_size);

    HALT_ON_ERRORCOND(sl_rt_size > 0x200000); /* 2M */

#ifndef __SKIP_BOOTLOADER_HASH__
    /* runtime */
    print_hex("    INIT(early): *UNTRUSTED* gold runtime: ",
              g_init_gold.sha_runtime, SHA_DIGEST_LENGTH);
    hashandprint("    INIT(early): *UNTRUSTED* comp runtime: ",
                 (u8*)hypervisor_image_baseaddress+0x200000, sl_rt_size-0x200000);
    /* SL low 64K */
    print_hex("    INIT(early): *UNTRUSTED* gold SL low 64K: ",
              g_init_gold.sha_slbelow64K, SHA_DIGEST_LENGTH);
    hashandprint("    INIT(early): *UNTRUSTED* comp SL low 64K: ",
                 (u8*)hypervisor_image_baseaddress, 0x10000);
    /* SL above 64K */
    print_hex("    INIT(early): *UNTRUSTED* gold SL above 64K: ",
              g_init_gold.sha_slabove64K, SHA_DIGEST_LENGTH);
    hashandprint("    INIT(early): *UNTRUSTED* comp SL above 64K): ",
                 (u8*)hypervisor_image_baseaddress+0x10000, 0x200000-0x10000);
#endif /* !__SKIP_BOOTLOADER_HASH__ */

    //print out stats
    printf("INIT(early): relocated hypervisor binary image to 0x%08x\n", hypervisor_image_baseaddress);
    printf("INIT(early): 2M aligned size = 0x%08lx\n", PAGE_ALIGN_UP_2M((mod_array[0].mod_end - mod_array[0].mod_start)));
    printf("INIT(early): un-aligned size = 0x%08x\n", mod_array[0].mod_end - mod_array[0].mod_start);

    //fill in "sl" parameter block
    {
        //"sl" parameter block is at hypervisor_image_baseaddress + 0x10000
        slpb = (SL_PARAMETER_BLOCK *)((u32)hypervisor_image_baseaddress + 0x10000);
        HALT_ON_ERRORCOND(slpb->magic == SL_PARAMETER_BLOCK_MAGIC);
        slpb->errorHandler = 0;
        slpb->isEarlyInit = 1;    //this is an "early" init
        slpb->numE820Entries = grube820list_numentries;
        //memcpy((void *)&slpb->e820map, (void *)&grube820list, (sizeof(GRUBE820) * grube820list_numentries));
		memcpy((void *)&slpb->memmapbuffer, (void *)&grube820list, (sizeof(GRUBE820) * grube820list_numentries));
        slpb->numCPUEntries = pcpus_numentries;
        //memcpy((void *)&slpb->pcpus, (void *)&pcpus, (sizeof(PCPU) * pcpus_numentries));
        memcpy((void *)&slpb->cpuinfobuffer, (void *)&pcpus, (sizeof(PCPU) * pcpus_numentries));
        slpb->runtime_size = (mod_array[0].mod_end - mod_array[0].mod_start) - PAGE_SIZE_2M;
        slpb->runtime_osbootmodule_base = mod_array[1].mod_start;
        slpb->runtime_osbootmodule_size = (mod_array[1].mod_end - mod_array[1].mod_start);
        slpb->runtime_osbootdrive = get_tboot_boot_drive();

		//check if we have an optional app module and if so populate relevant SLPB
		//fields
		{
			u32 i, start, bytes;
			slpb->runtime_appmodule_base= 0;
			slpb->runtime_appmodule_size= 0;

			//we search from module index 2 upto and including mods_count-1
			//and grab the first non-SINIT module in the list
			for(i=2; i < mods_count; i++) {
				start = mod_array[i].mod_start;
				bytes = mod_array[i].mod_end - start;
#ifdef __DRT__
				if (is_sinit_acmod((void*) start, bytes, false)) {
					continue;
				}
#endif /* __DRT__ */
				/* Found app module */
				slpb->runtime_appmodule_base = start;
				slpb->runtime_appmodule_size = bytes;
				printf("INIT(early): found app module, base=0x%08x, size=0x%08x\n",
						slpb->runtime_appmodule_base, slpb->runtime_appmodule_size);
				break;
			}
		}

#if defined (__DEBUG_SERIAL__)
        slpb->uart_config = g_uart_config;
#endif
        strncpy(slpb->cmdline, (const char *)mbi->cmdline, sizeof(slpb->cmdline));
    }

    //switch to MP mode
    //setup Master-ID Table (MIDTABLE)
    {
        int i;
        for(i=0; i < (int)pcpus_numentries; i++){
            midtable[midtable_numentries].cpu_lapic_id = pcpus[i].lapic_id;
            midtable[midtable_numentries].vcpu_vaddr_ptr = 0;
            midtable_numentries++;
        }
    }

    //setup vcpus
    setupvcpus(cpu_vendor, midtable, midtable_numentries);

#ifndef __SKIP_INIT_SMP__
    //wakeup all APs
    if(midtable_numentries > 1)
        wakeupAPs();
#endif /* __SKIP_INIT_SMP__ */

    //fall through and enter mp_cstartup via init_core_lowlevel_setup
    init_core_lowlevel_setup();

    printf("INIT(early): error(fatal), should never come here!\n");
    HALT();
}

//---isbsp----------------------------------------------------------------------
//returns 1 if the calling CPU is the BSP, else 0
u32 isbsp(void){
    u32 eax, edx;
    //read LAPIC base address from MSR
    rdmsr(MSR_APIC_BASE, &eax, &edx);
    HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G

    if(eax & 0x100)
        return 1;
    else
        return 0;
}


//---CPUs must all have their microcode cleared for SKINIT to be successful-----
void svm_clear_microcode(VCPU *vcpu){
    u32 ucode_rev;
    u32 dummy=0;

    // Current microcode patch level available via MSR read
    rdmsr(MSR_AMD64_PATCH_LEVEL, &ucode_rev, &dummy);
    printf("CPU(0x%02x): existing microcode version 0x%08x\n", vcpu->id, ucode_rev);

    if(ucode_rev != 0) {
        wrmsr(MSR_AMD64_PATCH_CLEAR, dummy, dummy);
        printf("CPU(0x%02x): microcode CLEARED\n", vcpu->id);
    }
}


#ifndef __SKIP_INIT_SMP__
u32 cpus_active=0; //number of CPUs that are awake, should be equal to
//midtable_numentries -1 if all went well with the
//MP startup protocol
u32 lock_cpus_active=1; //spinlock to access the above
#elif defined(__DRT__)
	#error "__SKIP_INIT_SMP__ not supported when __DRT__"
#endif /* __SKIP_INIT_SMP__ */


//------------------------------------------------------------------------------
//all cores enter here
void mp_cstartup (VCPU *vcpu){
    //sanity, we should be an Intel or AMD core
    HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_INTEL ||
           vcpu->cpu_vendor == CPU_VENDOR_AMD);

    if(isbsp()){
        //clear microcode if AMD CPU
        if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
            printf("BSP(0x%02x): Clearing microcode...\n", vcpu->id);
            svm_clear_microcode(vcpu);
            printf("BSP(0x%02x): Microcode clear.\n", vcpu->id);

            if(!svm_prepare_tpm()) {
                printf("BSP(0x%02x): ERROR: svm_prepare_tpm FAILED.\n", vcpu->id);
                // XXX TODO HALT();
            }
        }

        printf("BSP(0x%02x): Rallying APs...\n", vcpu->id);

#ifndef __SKIP_INIT_SMP__
        //increment a CPU to account for the BSP
        spin_lock(&lock_cpus_active);
        cpus_active++;
        spin_unlock(&lock_cpus_active);

        //wait for cpus_active to become midtable_numentries -1 to indicate
        //that all APs have been successfully started
        while (cpus_active < midtable_numentries) {
            xmhf_cpu_relax();
        }
#endif /* __SKIP_INIT_SMP__ */

        //put all APs in INIT state

        printf("BSP(0x%02x): APs ready, doing DRTM...\n", vcpu->id);
        do_drtm(vcpu, hypervisor_image_baseaddress, sl_rt_size); // this function will not return

        printf("BSP(0x%02x): FATAL, should never be here!\n", vcpu->id);
        HALT();

    }else{
        //clear microcode if AMD CPU
        if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
            printf("AP(0x%02x): Clearing microcode...\n", vcpu->id);
            svm_clear_microcode(vcpu);
            printf("AP(0x%02x): Microcode clear.\n", vcpu->id);
        }

        printf("AP(0x%02x): Waiting for DRTM establishment...\n", vcpu->id);

#ifndef __SKIP_INIT_SMP__
        //update the AP startup counter
        spin_lock(&lock_cpus_active);
        cpus_active++;
        spin_unlock(&lock_cpus_active);
#endif /* __SKIP_INIT_SMP__ */

        /*
         * Note: calling printf() here may lead to deadlock. After BSP
         * see cpus_active = nproc, it calls send_init_ipi_to_all_APs() to send
         * INIT interrupt to APs. If an AP receives the INIT interrupt while
         * holding the printf lock, BSP will deadlock when printing anything
         * afterwards.
         */

        HALT();
    }


}
