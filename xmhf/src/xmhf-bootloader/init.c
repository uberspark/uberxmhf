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
#include <xmhf-debug-x86.h>
#include <xmhfcrypto.h>
#include <tpm.h>
#include <cmdline.h>

#include "platform/x86pc/include/common/_multiboot.h"		//multiboot
#include "cpu/x86/include/common/_processor.h"  	//CPU
#include "cpu/x86/include/common/_msr.h"        	//model specific registers
#include "cpu/x86/include/common/_paging.h"     	//MMU
#include "cpu/x86/include/common/_io.h"         	//legacy I/O
#include "cpu/x86/include/intel/txt/_txt.h"			//Trusted eXecution Technology (SENTER support)
#include "platform/x86pc/include/common/_acpi.h"			//ACPI glue
#include "platform/x86pc/include/common/_memaccess.h"	//platform memory access
#include "platform/x86pc/include/common/_biosdata.h"	//BIOS data areas

//the vcpu structure which holds the current state of a core
typedef struct _bootvcpu {
  u32 esp;                //used to establish stack for the CPU
  u32 id;                 //LAPIC id of the core
  u32 cpu_vendor;					//Intel or AMD
  u32 isbsp;							//1 if this core is BSP else 0
} __attribute__((packed)) BOOTVCPU;

#define SIZE_STRUCT_BOOTVCPU    (sizeof(struct _bootvcpu))

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

//master-id table which holds LAPIC ID to BOOTVCPU mapping for each physical core
MIDTAB midtable[MAX_MIDTAB_ENTRIES] __attribute__(( section(".data") ));

//number of physical cores in the system
u32 midtable_numentries=0;

//BOOTVCPU buffers for all cores
BOOTVCPU vcpubuffers[MAX_VCPU_ENTRIES] __attribute__(( section(".data") ));

//initial stacks for all cores
u8 cpustacks[RUNTIME_STACK_SIZE * MAX_PCPU_ENTRIES] __attribute__(( section(".stack") ));

XMHF_BOOTINFO *xslbootinfo = NULL;

/* TODO: refactor to eliminate a lot of these globals, or at least use
 * static where appropriate */
static u8 *g_sinit_module_ptr = NULL;
static u32 g_sinit_module_size = 0;

extern void init_core_lowlevel_setup(void);

extern char g_cmdline[MAX_CMDLINE_SIZE];
extern void tboot_parse_cmdline(void);
//extern void get_tboot_loglvl(void);
//extern void get_tboot_log_targets(void);
extern bool get_tboot_serial(void);
extern void get_tboot_baud(void);
extern void get_tboot_fmt(void);

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
        printf("\nFatal error with SMP detection. Halting!");
        HALT();
    }
}


//---microsecond delay----------------------------------------------------------
void udelay(u32 usecs){
    u8 val;
    u32 latchregval;  

    //enable 8254 ch-2 counter
    val = inb(0x61);
    val &= 0x0d; //turn PC speaker off
    val |= 0x01; //turn on ch-2
    outb(val, 0x61);
  
    //program ch-2 as one-shot
    outb(0xB0, 0x43);
  
    //compute appropriate latch register value depending on usecs
    latchregval = (1193182 * usecs) / 1000000;

    //write latch register to ch-2
    val = (u8)latchregval;
    outb(val, 0x42);
    val = (u8)((u32)latchregval >> (u32)8);
    outb(val , 0x42);
  
    //wait for countdown
    while(!(inb(0x61) & 0x20));
  
    //disable ch-2 counter
    val = inb(0x61);
    val &= 0x0c;
    outb(val, 0x61);
}


//---INIT IPI routine-----------------------------------------------------------
void send_init_ipi_to_all_APs(void) {
    u32 eax, edx;
    volatile u32 *icr;
    u32 timeout = 0x01000000;
  
    //read LAPIC base address from MSR
    rdmsr(MSR_APIC_BASE, &eax, &edx);
    HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G
    printf("\nLAPIC base and status=0x%08x", eax);
    
    icr = (u32 *) (((u32)eax & 0xFFFFF000UL) + 0x300);

    //send INIT
    printf("\nSending INIT IPI to all APs...");
    *icr = 0x000c4500UL;
    udelay(10000);
    //wait for command completion
    {
        u32 val;
        do{
            val = *icr;
        }while(--timeout > 0 && (val & 0x1000) );
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
        printf("\n%s: no E820 map provided. HALT!", __FUNCTION__);
        HALT();
    }
  
    //zero out grub e820 list
    memset((void *)&grube820list, 0, sizeof(GRUBE820)*MAX_E820_ENTRIES);

    //grab e820 list into grube820list
    {
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
            printf("\n0x%08x%08x, size=0x%08x%08x (%u)", 
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
                    printf("\n%s: E820 parsing error (64-bit length for < 4GB). HALT!");
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
            printf("\n%s: unable to find E820 memory for SL+runtime. HALT!");
            HALT();
        }

		//entry number we need to split is indexed by i
		printf("\nproceeding to revise E820...");
		
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

		printf("\nE820 revision complete.");
			
		//debug: print grube820list
		{
			u32 i;
			printf("\nrevised system E820 map follows:\n");
			for(i=0; i < grube820list_numentries; i++){
				printf("\n0x%08x%08x, size=0x%08x%08x (%u)", 
					   grube820list[i].baseaddr_high, grube820list[i].baseaddr_low,
					   grube820list[i].length_high, grube820list[i].length_low,
					   grube820list[i].type);
			}
		}


        return slruntimephysicalbase;
    }
  
}

/* Run tests to determine if platform supports TXT.  Note that this
 * enables SMX on the platform, but is safe to run more than once. */
/* Based primarily on tboot-20101005's txt/verify.c */
bool txt_supports_txt(void) {

    u32 cpuid_ext_feat_info, dummy;
    u64 feat_ctrl_msr;
    capabilities_t cap;

    cpuid(1, &dummy, &dummy, &cpuid_ext_feat_info, &dummy);
    feat_ctrl_msr = rdmsr64(MSR_EFCR);

    /* Check for VMX support */
    if ( !(cpuid_ext_feat_info & CPUID_X86_FEATURE_VMX) ) {
        printf("ERR: CPU does not support VMX\n");
        return false;
    }
    printf("CPU is VMX-capable\n");
    /* and that VMX is enabled in the feature control MSR */
    if ( !(feat_ctrl_msr & IA32_FEATURE_CONTROL_MSR_ENABLE_VMX_IN_SMX) ) {
        printf("ERR: VMXON disabled by feature control MSR (%llx)\n",
               feat_ctrl_msr);
        return false;
    }
    
    
    /* Check that processor supports SMX instructions */
    if ( !(cpuid_ext_feat_info & CPUID_X86_FEATURE_SMX) ) {
        printf("ERR: CPU does not support SMX\n");
        return false;
    }
    printf("CPU is SMX-capable\n");
    
    /* and that SENTER (w/ full params) is enabled */
    if ( !(feat_ctrl_msr & (IA32_FEATURE_CONTROL_MSR_ENABLE_SENTER |
                            IA32_FEATURE_CONTROL_MSR_SENTER_PARAM_CTL)) ) {
        printf("ERR: SENTER disabled by feature control MSR (%llx)\n",
               feat_ctrl_msr);
        return false;
    }
    printf("SENTER should work.\n");

    /* testing for chipset support requires enabling SMX on the processor */
    write_cr4(read_cr4() | CR4_SMXE);
    printf("SMX enabled in CR4\n");

    /* Verify that an TXT-capable chipset is present and check that
     * all needed SMX capabilities are supported. */

    cap = (capabilities_t)__getsec_capabilities(0);
    if(!cap.chipset_present) {
        printf("ERR: TXT-capable chipset not present\n");
        return false;
    }        
    if (!(cap.senter && cap.sexit && cap.parameters && cap.smctrl &&
          cap.wakeup)) {
        printf("ERR: insufficient SMX capabilities (0x%08x)\n", cap._raw);
        return false;
    }    
    printf("TXT chipset and all needed capabilities (0x%08x) present\n", cap._raw);    
    
    return true;
}

/* Inspired by tboot-20101005/tboot/txt/verify.c */
tb_error_t txt_verify_platform(void)
{
    txt_heap_t *txt_heap;
    txt_ests_t ests;

    printf("txt_verify_platform\n");
    
    /* check TXT supported */
    if(!txt_supports_txt()) {
        printf("FATAL ERROR: TXT not suppported\n");
        HALT();
    }    

    /* check is TXT_RESET.STS is set, since if it is SENTER will fail */
    ests = (txt_ests_t)read_pub_config_reg(TXTCR_ESTS);
    if ( ests.txt_reset_sts ) {
        printf("TXT_RESET.STS is set and SENTER is disabled (%llx)\n",
               ests._raw);
        return TB_ERR_SMX_NOT_SUPPORTED;
    }

    /* verify BIOS to OS data */
    txt_heap = get_txt_heap();
    if ( !verify_bios_data(txt_heap) )
        return TB_ERR_FATAL;

    return TB_ERR_NONE;
}


/* Read values in TXT status registers */
/* Some tboot-20101005 code from tboot/txt/errors.c */
void txt_status_regs(void) {
    txt_errorcode_t err;
    txt_ests_t ests;
    txt_e2sts_t e2sts;
    txt_errorcode_sw_t sw_err;
    acmod_error_t acmod_err;

    err = (txt_errorcode_t)read_pub_config_reg(TXTCR_ERRORCODE);
    printf("TXT.ERRORCODE=%llx\n", err._raw);

    /* AC module error (don't know how to parse other errors) */
    if ( err.valid ) {
        if ( err.external == 0 )       /* processor error */
            printf("\t processor error %x\n", (uint32_t)err.type);
        else {                         /* external SW error */
            sw_err._raw = err.type;
            if ( sw_err.src == 1 )     /* unknown SW error */
                printf("unknown SW error %x:%x\n", sw_err.err1, sw_err.err2);
            else {                     /* ACM error */
                acmod_err._raw = sw_err._raw;
                printf("AC module error : acm_type=%x, progress=%02x, "
                       "error=%x\n", acmod_err.acm_type, acmod_err.progress,
                       acmod_err.error);
                /* error = 0x0a, progress = 0x0d => error2 is a TPM error */
                if ( acmod_err.error == 0x0a && acmod_err.progress == 0x0d )
                    printf("TPM error code = %x\n", acmod_err.error2);
            }
        }
    }

    /*
     * display LT.ESTS error
     */
    ests = (txt_ests_t)read_pub_config_reg(TXTCR_ESTS);
    printf("LT.ESTS=%llx\n", ests._raw);

    /*
     * display LT.E2STS error
     * - only valid if LT.WAKE-ERROR.STS set in LT.STS reg
     */
    if ( ests.txt_wake_error_sts ) {
        e2sts = (txt_e2sts_t)read_pub_config_reg(TXTCR_E2STS);
        printf("LT.E2STS=%llx\n", e2sts._raw);
    }    
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

    txt_status_regs();
    
    if((err = txt_verify_platform()) != TB_ERR_NONE) {
        printf("ERROR: txt_verify_platform returned 0x%08x\n", (u32)err);
        return false;
    }
    if(!txt_prepare_cpu()) {
        printf("ERROR: txt_prepare_cpu failed.\n");
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
        printf("Checking whether MBI module %i is SINIT...\n", i);
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
static bool svm_prepare_cpu(void) __attribute__((unused));
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

//---do_drtm--------------------------------------------------------------------
//this establishes a dynamic root of trust
//inputs: 
//cpu_vendor = intel or amd
//slbase= physical memory address of start of sl
void do_drtm(BOOTVCPU __attribute__((unused))*vcpu, u32 slbase, size_t mle_size __attribute__((unused))){
#ifdef __MP_VERSION__
    HALT_ON_ERRORCOND(vcpu->id == 0);
    //send INIT IPI to all APs 
    send_init_ipi_to_all_APs();
    printf("\nINIT(early): sent INIT IPI to APs");
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
        printf("\nINIT(early): transferring control to SL via SKINIT...");
		#ifndef PERF_CRIT
        if(NULL != xslbootinfo) {
            __asm__ __volatile__ (
                "cpuid\r\n"
                "cpuid\r\n"
                "cpuid\r\n"
                "rdtsc\r\n"
                : "=A"(xslbootinfo->rdtsc_before_drtm)
                : /* no inputs */
                : "ebx","ecx");
        }
		#endif
        skinit((u32)slbase);
    } else {
        printf("\n******  INIT(early): Begin TXT Stuff  ******\n");        
        txt_do_senter((void*)(slbase+3*PAGE_SIZE_4K), TEMPORARY_HARDCODED_MLE_SIZE);
        printf("\nINIT(early): error(fatal), should never come here!");
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
		printf("\nslbase=0x%08x, sl_entry_point_offset=0x%08x", (u32)slbase, *sl_entry_point_offset);
		sl_entry_point = (u32)slbase + (u32) (*sl_entry_point_offset);
		invokesl = (FCALL)(u32)sl_entry_point;
		printf("\nSL entry point to transfer control to: 0x%08x", invokesl);
		invokesl();
        printf("\nINIT(early): error(fatal), should never come here!");
        HALT();
	}	
#endif    
 
}


void setupvcpus(u32 cpu_vendor, MIDTAB *midtable, u32 midtable_numentries){
    u32 i;
    BOOTVCPU *vcpu;
  
    printf("\n%s: cpustacks range 0x%08x-0x%08x in 0x%08x chunks",
           __FUNCTION__, (u32)cpustacks, (u32)cpustacks + (RUNTIME_STACK_SIZE * MAX_VCPU_ENTRIES),
           RUNTIME_STACK_SIZE);
    printf("\n%s: vcpubuffers range 0x%08x-0x%08x in 0x%08x chunks",
           __FUNCTION__, (u32)vcpubuffers, (u32)vcpubuffers + (SIZE_STRUCT_BOOTVCPU * MAX_VCPU_ENTRIES),
           SIZE_STRUCT_BOOTVCPU);
          
    for(i=0; i < midtable_numentries; i++){
        vcpu = (BOOTVCPU *)((u32)vcpubuffers + (u32)(i * SIZE_STRUCT_BOOTVCPU));
        memset((void *)vcpu, 0, sizeof(BOOTVCPU));
    
        vcpu->cpu_vendor = cpu_vendor;
    
        vcpu->esp = ((u32)cpustacks + (i * RUNTIME_STACK_SIZE)) + RUNTIME_STACK_SIZE;    
        vcpu->id = midtable[i].cpu_lapic_id;

        midtable[i].vcpu_vaddr_ptr = (u32)vcpu;
        printf("\nCPU #%u: vcpu_vaddr_ptr=0x%08x, esp=0x%08x", i, midtable[i].vcpu_vaddr_ptr,
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
    //printf("\nLAPIC base and status=0x%08x", eax);
    
    icr = (u32 *) (((u32)eax & 0xFFFFF000UL) + 0x300);
    
    {
        extern u32 _ap_bootstrap_start[], _ap_bootstrap_end[];
        memcpy((void *)0x10000, (void *)_ap_bootstrap_start, (u32)_ap_bootstrap_end - (u32)_ap_bootstrap_start + 1);
    }

    //our test code is at 1000:0000, we need to send 10 as vector
    //send INIT
    printf("\nSending INIT IPI to all APs...");
    *icr = 0x000c4500UL;
    udelay(10000);
    //wait for command completion
    {
        u32 val;
        do{
            val = *icr;
        }while( (val & 0x1000) );
    }
    printf("Done.");

    //send SIPI (twice as per the MP protocol)
    {
        int i;
        for(i=0; i < 2; i++){
            printf("\nSending SIPI-%u...", i);
            *icr = 0x000c4610UL;
            udelay(200);
            //wait for command completion
            {
                u32 val;
                do{
                    val = *icr;
                }while( (val & 0x1000) );
            }
            printf("Done.");
        }
    }    
    
    printf("\nAPs should be awake!");
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
    
    printf("\nINIT:TPM: prepare_tpm starting.");
    //dump_locality_access_regs();
    xmhf_tpm_deactivate_all_localities();
    //dump_locality_access_regs();
    
    if(TPM_SUCCESS == tpm_wait_cmd_ready(locality)) {
        printf("INIT:TPM: successfully opened in Locality %d.\n", locality);            
    } else {
        printf("INIT:TPM: ERROR: Locality %d could not be opened.\n", locality);
        ret = false;
    }
    xmhf_tpm_deactivate_all_localities();
    //dump_locality_access_regs();
    printf("\nINIT:TPM: prepare_tpm done.");

    return ret;
}

//---init main----------------------------------------------------------------
void cstartup(multiboot_info_t *mbi){
    module_t *mod_array;
    u32 mods_count;
	size_t hypapp_size;
	
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
	printf("\neXtensible Modular Hypervisor Framework (XMHF) %s", ___XMHF_BUILD_VERSION___);
	printf("\nBuild revision: %s\n", ___XMHF_BUILD_REVISION___);
	
    printf("\nXMHF boot-loader: initializing, total modules=%u", mods_count);

	//we need at least 2 modules passed to us via GRUB, the hypapp binary and the guest OS boot-sector. 
	//If we don't have the bare minimum, bail out early
	if(mods_count < 2){
		printf("\nXMHF boot-loader: Halting, you need a hypapp and the guest OS boot sector at bare minimum!");
		HALT(); 		
	}

    //check CPU type (Intel vs AMD)
    cpu_vendor = get_cpu_vendor_or_die(); // HALT()'s if unrecognized    

    if(CPU_VENDOR_INTEL == cpu_vendor) {
        printf("\nINIT(early): detected an Intel CPU");
        
        /* Intel systems require an SINIT module */
        if(!txt_parse_sinit(mod_array, mods_count)) {
            printf("\nINIT(early): FATAL ERROR: Intel CPU without SINIT module!\n");
            HALT();
        }            
    } else if(CPU_VENDOR_AMD == cpu_vendor) {
        printf("\nINIT(early): detected an AMD CPU");
    } else {
        printf("\nINIT(early): Dazed and confused: Unknown CPU vendor %d\n", cpu_vendor);
    }
    
    //deal with MP and get CPU table
    dealwithMP();

    //check (and revise) platform E820 memory map to see if we can
    //load at __TARGET_BASE_SL 
    //sl_rt_size = mod_array[0].mod_start - __TARGET_BASE_BOOTLOADER + __TARGET_SIZE_BOOTLOADER;
    sl_rt_size = (mod_array[0].mod_start - __TARGET_BASE_BOOTLOADER) - __TARGET_SIZE_BOOTLOADER;
    hypapp_size = mod_array[0].mod_end - mod_array[0].mod_start;
    hypervisor_image_baseaddress = dealwithE820(mbi, PAGE_ALIGN_UP2M(sl_rt_size) + PAGE_ALIGN_UP2M(hypapp_size) ); 

	//sanity check memory map and limits
		//ensure we are loading at 256M
		HALT_ON_ERRORCOND( (hypervisor_image_baseaddress == __TARGET_BASE_SL) );
		
		//load address of XMHF bootloader = 30MB
		//sizeof ( XMHF bootloader) = 2MB
		//sizeof ( XMHF secureloader+ XMHF runtime + hypapp binary + guest OS boot-sector + SINIT module (if any) + hypapp specific modules (if any) ) 
		//should not be greater than 224MB since we will be loading our system at absolute address 256MB and our current memcpy does not tackle overlaps
		if ( mod_array[mods_count-1].mod_end >= __TARGET_BASE_SL ){
			printf("\nXMHF boot-loader: Halting! XMHF load memory map limits violated. TOMM=0x%08x", mod_array[mods_count-1].mod_end);
			HALT();
		}

		//SL+core memory map is from 0x10000000-0x1D000000
		if(sl_rt_size > (__TARGET_BASE_XMHFHYPAPP - __TARGET_BASE_SL) ){
			printf("\nXMHF boot-loader: Halting! XMHF SL + core memory limit overflow. size=%08x (max:%08x)", sl_rt_size, (__TARGET_BASE_XMHFHYPAPP - __TARGET_BASE_SL));
			HALT();
		}
		
		//hypapp memory map is from 0x1D000000-0x20000000
		if( hypapp_size > __TARGET_SIZE_XMHFHYPAPP ){
			printf("\nXMHF boot-loader: Halting! XMHF hypapp memory limit overflow. size=%08x (max:%08x)", hypapp_size, __TARGET_SIZE_XMHFHYPAPP);
			HALT();
		}
		

    //relocate the SL+core runtime+hyypapp binaries to corresponding memory regions
    memcpy((void*)__TARGET_BASE_SL, (void*)(__TARGET_BASE_BOOTLOADER+__TARGET_SIZE_BOOTLOADER), sl_rt_size);
	memcpy((void*)__TARGET_BASE_XMHFHYPAPP, (void *)mod_array[0].mod_start, hypapp_size);

	////DMA protect SL+runtime via VTd PMRs
	//if(cpu_vendor == CPU_VENDOR_INTEL){
	//	extern bool vtdinit_dmaprotect(u32 membase, u32 size);
	//	vtdinit_dmaprotect(__TARGET_BASE_SL, sl_rt_size);
	//}
	
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

    
    //print out stats
    printf("\nINIT(early): relocated hypervisor binary image to 0x%08x", hypervisor_image_baseaddress);
    printf("\nINIT(early): 2M aligned size = 0x%08lx", PAGE_ALIGN_UP2M((mod_array[0].mod_end - mod_array[0].mod_start)));
    printf("\nINIT(early): un-aligned size = 0x%08x", mod_array[0].mod_end - mod_array[0].mod_start);
    
    //fill in "sl" parameter block
    {
        //"sl" parameter block is at hypervisor_image_baseaddress + 0x10000
        xslbootinfo = (XMHF_BOOTINFO *)((u32)hypervisor_image_baseaddress + 0x10000);
        HALT_ON_ERRORCOND(xslbootinfo->magic == SL_PARAMETER_BLOCK_MAGIC);
        xslbootinfo->memmapinfo_numentries = grube820list_numentries;
        HALT_ON_ERRORCOND(xslbootinfo->memmapinfo_numentries > 64);
		memcpy((void *)&xslbootinfo->memmapinfo_buffer, (void *)&grube820list, (sizeof(GRUBE820) * grube820list_numentries));         
        xslbootinfo->cpuinfo_numentries = pcpus_numentries;
        HALT_ON_ERRORCOND(xslbootinfo->cpuinfo_numentries > 8);
        memcpy((void *)&xslbootinfo->cpuinfo_buffer, (void *)&pcpus, (sizeof(PCPU) * pcpus_numentries));
        //xslbootinfo->runtime_size = sl_rt_size - PAGE_SIZE_2M;
        xslbootinfo->size = sl_rt_size;
        xslbootinfo->richguest_bootmodule_base = mod_array[1].mod_start;
        xslbootinfo->richguest_bootmodule_size = (mod_array[1].mod_end - mod_array[1].mod_start); 

		/*//check if we have an optional app module and if so populate relevant SLPB
		//fields
		{
			u32 i, bytes;
			xslbootinfo->runtime_appmodule_base= 0;
			xslbootinfo->runtime_appmodule_size= 0;

			//we search from module index 2 upto and including mods_count-1
			//and grab the first non-SINIT module in the list
			for(i=2; i < mods_count; i++) {
				bytes = mod_array[i].mod_end - mod_array[i].mod_start;
				if(!is_sinit_acmod((void*)mod_array[i].mod_start, bytes, false)){
						xslbootinfo->runtime_appmodule_base= mod_array[i].mod_start;
						xslbootinfo->runtime_appmodule_size= bytes;
						printf("\nINIT(early): found app module, base=0x%08x, size=0x%08x",
								xslbootinfo->runtime_appmodule_base, xslbootinfo->runtime_appmodule_size);
						break;
				}
			}
		}*/

#if defined (__DEBUG_SERIAL__)
        //xslbootinfo->uart_config = g_uart_config;
        memcpy(&xslbootinfo->debugcontrol_buffer, &g_uart_config, sizeof(uart_config_t));
#endif
        strncpy(xslbootinfo->cmdline_buffer, (const char *)mbi->cmdline, sizeof(xslbootinfo->cmdline));
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
    
    //wakeup all APs
    if(midtable_numentries > 1)
        wakeupAPs();

    //fall through and enter mp_cstartup via init_core_lowlevel_setup
    init_core_lowlevel_setup();
        
    printf("\nINIT(early): error(fatal), should never come here!");
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
void svm_clear_microcode(BOOTVCPU *vcpu){
    u32 ucode_rev;
    u32 dummy=0;

    // Current microcode patch level available via MSR read
    rdmsr(MSR_AMD64_PATCH_LEVEL, &ucode_rev, &dummy);
    printf("\nCPU(0x%02x): existing microcode version 0x%08x", vcpu->id, ucode_rev);
    
    if(ucode_rev != 0) {
        wrmsr(MSR_AMD64_PATCH_CLEAR, dummy, dummy);
        printf("\nCPU(0x%02x): microcode CLEARED", vcpu->id);
    }
}


u32 cpus_active=0; //number of CPUs that are awake, should be equal to
//midtable_numentries -1 if all went well with the
//MP startup protocol
u32 lock_cpus_active=1; //spinlock to access the above


//------------------------------------------------------------------------------
//all cores enter here 
void mp_cstartup (BOOTVCPU *vcpu){
    //sanity, we should be an Intel or AMD core
    HALT_ON_ERRORCOND(vcpu->cpu_vendor == CPU_VENDOR_INTEL ||
           vcpu->cpu_vendor == CPU_VENDOR_AMD);

    if(isbsp()){
        //clear microcode if AMD CPU
        if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
            printf("\nBSP(0x%02x): Clearing microcode...", vcpu->id);
            svm_clear_microcode(vcpu);
            printf("\nBSP(0x%02x): Microcode clear.", vcpu->id);

            if(!svm_prepare_tpm()) {
                printf("\nBSP(0x%02x): ERROR: svm_prepare_tpm FAILED.", vcpu->id);
                // XXX TODO HALT();
            }            
        }
         
        printf("\nBSP(0x%02x): Rallying APs...", vcpu->id);

        //increment a CPU to account for the BSP
        spin_lock(&lock_cpus_active);
        cpus_active++;
        spin_unlock(&lock_cpus_active);

        //wait for cpus_active to become midtable_numentries -1 to indicate
        //that all APs have been successfully started
        while(cpus_active < midtable_numentries);


        //put all APs in INIT state
        
        printf("\nBSP(0x%02x): APs ready, doing DRTM...", vcpu->id);
        do_drtm(vcpu, hypervisor_image_baseaddress, sl_rt_size); // this function will not return
    
        printf("\nBSP(0x%02x): FATAL, should never be here!", vcpu->id);
        HALT();
    
    }else{
        //clear microcode if AMD CPU
        if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
            printf("\nAP(0x%02x): Clearing microcode...", vcpu->id);
            svm_clear_microcode(vcpu);
            printf("\nAP(0x%02x): Microcode clear.", vcpu->id);
        }
    
        //update the AP startup counter
        spin_lock(&lock_cpus_active);
        cpus_active++;
        spin_unlock(&lock_cpus_active);

        printf("\nAP(0x%02x): Waiting for DRTM establishment...", vcpu->id);
 
        HALT();               
    }


}
