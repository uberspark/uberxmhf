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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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
#include <target.h>
#include <txt.h>
#include <sha1.h>
#include <tpm.h>

#include "i5_i7_dual_sinit_18.h" // XXX TODO read this from MBI stuff

//---forward prototypes---------------------------------------------------------
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


extern init_core_lowlevel_setup(void);


//---MP config table handling---------------------------------------------------
void dealwithMP(void){
    if(!smp_getinfo(&pcpus, &pcpus_numentries)){
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
    ASSERT( edx == 0 ); //APIC is below 4G
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
u32 dealwithE820(multiboot_info_t *mbi, u32 runtimesize){
    //check if GRUB has a valid E820 map
    if(!(mbi->flags & MBI_MEMMAP)){
        printf("\n%s: FATAL error, no E820 map provided!", __FUNCTION__);
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
        printf("\nOriginal E820 map follows:\n");
        for(i=0; i < grube820list_numentries; i++){
            printf("\n0x%08x%08x, size=0x%08x%08x (%u)", 
                   grube820list[i].baseaddr_high, grube820list[i].baseaddr_low,
                   grube820list[i].length_high, grube820list[i].length_low,
                   grube820list[i].type);
        }
  
    }
  
    //traverse e820 list backwards to find an entry with type=0x1 (free)
    //with free amount of memory for runtime
    {
        u32 foundentry=0;
        u32 runtimephysicalbase=0;
        int i;
     
        //#define ADDR_4GB  (0xFFFFFFFFUL)
        for(i= (int)(grube820list_numentries-1); i >=0; i--){
            u32 baseaddr, size;
            baseaddr = grube820list[i].baseaddr_low;
            //size = PAGE_ALIGN_4K(grube820list[i].length_low);  
            size = grube820list[i].length_low;
    
            if(grube820list[i].type == 0x1){ //free memory?
                if(grube820list[i].baseaddr_high) //greater than 4GB? then skip
                    continue; 

                if(grube820list[i].length_high){
                    printf("\noops 64-bit length unhandled!");
                    HALT();
                }
      
                runtimephysicalbase = PAGE_ALIGN_2M((u32)baseaddr + size) - runtimesize;

                if( runtimephysicalbase >= baseaddr ){
                    foundentry=1;
                    break;
                }
            }
        } 
    
        if(!foundentry){
            printf("\nFatal: unable to find E820 memory for runtime!");
            HALT();
        }

        //entry number we need to split is indexed by i, we need to
        //make place for 1 extra entry at position i
        if(grube820list_numentries == MAX_E820_ENTRIES){
            printf("\noops, exhausted max E820 entries!");
            HALT();
        }

        if(i == (int)(grube820list_numentries-1)){
            //if this is the last entry, we dont need memmove
            //deal with i and i+1
      
        }else{
            memmove( (void *)&grube820list[i+2], (void *)&grube820list[i+1], (grube820list_numentries-i-1)*sizeof(GRUBE820));
            memset (&grube820list[i+1], 0, sizeof(GRUBE820));
            //deal with i and i+1 
            {
                u32 sizetosplit= grube820list[i].length_low;
                u32 newsizeofiplusone = grube820list[i].baseaddr_low + sizetosplit - runtimephysicalbase;
                u32 newsizeofi = runtimephysicalbase - grube820list[i].baseaddr_low;
                grube820list[i].length_low = newsizeofi;
                grube820list[i+1].baseaddr_low = runtimephysicalbase;
                grube820list[i+1].type = 0x2;// reserved
                grube820list[i+1].length_low = newsizeofiplusone;
      
            }
        }
        grube820list_numentries++;
    
        return runtimephysicalbase;
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
    tb_error_t err;
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
        printf("TXT_RESET.STS is set and SENTER is disabled (0x%02Lx)\n",
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
    printf("TXT.ERRORCODE=%Lx\n", err._raw);

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
    printf("LT.ESTS=%Lx\n", ests._raw);

    /*
     * display LT.E2STS error
     * - only valid if LT.WAKE-ERROR.STS set in LT.STS reg
     */
    if ( ests.txt_wake_error_sts ) {
        e2sts = (txt_e2sts_t)read_pub_config_reg(TXTCR_E2STS);
        printf("LT.E2STS=%Lx\n", e2sts._raw);
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
    txt_launch_environment(i5_i7_dual_sinit_18, SINIT_HARDCODED_SIZE,
                           phys_mle_start, mle_size);
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
            printf("MCG[%d] = %Lx ERROR\n", i, mcg_stat);
            return false;
        }
    }
    
    printf("no machine check errors\n");

    /* clear microcode on all the APs */
/*     if (!init_all_aps()) */
/*         return false; */
/*     if (!clear_microcode()) */
/*         return false; */

    /* put all APs in INIT */
/*     if (!init_all_aps()) */
/*         return false; */

    /* all is well with the processor state */
    printf("CPU is ready for SKINIT\n");

    return true;
}

//---do_drtm--------------------------------------------------------------------
//this establishes a dynamic root of trust
//inputs: 
//cpu_vendor = intel or amd
//slbase= physical memory address of start of sl
void do_drtm(VCPU *vcpu, u32 slbase){
#ifdef __MP_VERSION__
    ASSERT(vcpu->id == 0);
    //send INIT IPI to all APs 
    send_init_ipi_to_all_APs();
    printf("\nINIT(early): sent INIT IPI to APs");
#endif  

    if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
        printf("\ncalling svm_prepare_cpu()...\n");
        if(!svm_prepare_cpu()) {
            printf("\nINIT(early): ERROR: svm_prepare_cpu FAILED!\n");
            HALT();
        }
        printf("\nINIT(early): sending additional INIT IPI to APs");
        send_init_ipi_to_all_APs();
        //issue SKINIT
        //our secure loader is the first 64K of the hypervisor image
        printf("\nINIT(early): transferring control to SL via SKINIT...");
        skinit((u32)slbase);
    } else {
/* SENTER enabled based on Makefile for now, since hypervisor cannot
 * fully boot due to MP and MTRR issues. */        
#ifdef __DO_SENTER__ 
        printf("\n******  INIT(early): Begin TXT Stuff  ******\n");        
        txt_do_senter((void*)(slbase+3*PAGE_SIZE_4K), TEMPORARY_HARDCODED_MLE_SIZE);
        printf("\nINIT(early): error(fatal), should never come here!");
        HALT();
#endif /* __DO_SENTER__ */
        printf("\nINIT(early): SENTER disabled in Makefile.");
        printf("\nINIT(early): transferring control to SL...");
        {    
            u32 entrypoint;
            u16 offset;
            offset = *((u16 *)slbase);
            entrypoint = slbase + (u32)offset;
            printf("\nINIT(early): SENTER stub, slbase=0x%08x, o=0x%04x, ep=0x%08x",
                   slbase, offset, entrypoint); 
            __asm__ __volatile__("cli\r\n"
                                 "movl %0, %%eax\r\n"
                                 "movl %1, %%ebx\r\n"
                                 "call *%%ebx\r\n"    
                                 : //no outputs
                                 : "r"(slbase), "r"(entrypoint)
                                 : "eax", "ebx"
                                 );
        }
        
        printf("\nINIT(early): error(fatal), should never come here!");
        HALT();
    }

}


void setupvcpus(u32 cpu_vendor, MIDTAB *midtable, u32 midtable_numentries){
    u32 i;
    VCPU *vcpu;
  
    printf("\n%s: cpustacks range 0x%08x-0x%08x in 0x%08x chunks",
           __FUNCTION__, (u32)cpustacks, (u32)cpustacks + (RUNTIME_STACK_SIZE * MAX_VCPU_ENTRIES),
           RUNTIME_STACK_SIZE);
    printf("\n%s: vcpubuffers range 0x%08x-0x%08x in 0x%08x chunks",
           __FUNCTION__, (u32)vcpubuffers, (u32)vcpubuffers + (SIZE_STRUCT_VCPU * MAX_VCPU_ENTRIES),
           SIZE_STRUCT_VCPU);
          
    for(i=0; i < midtable_numentries; i++){
        vcpu = (VCPU *)((u32)vcpubuffers + (u32)(i * SIZE_STRUCT_VCPU));
        memset((void *)vcpu, 0, sizeof(VCPU));
    
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
    ASSERT( edx == 0 ); //APIC is below 4G
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

void hashandprint(const char* prefix, const u8 *bytes, size_t len) {
    SHA_CTX ctx;
    u8 digest[SHA_DIGEST_LENGTH];

    SHA1_Init(&ctx);
    SHA1_Update(&ctx, bytes, len);
    SHA1_Final(digest, &ctx);

    print_hex(prefix, digest, SHA_DIGEST_LENGTH);

    /* Simulate PCR 17 value on AMD processor */
    if(len == 0x10000) {
        u8 zeros[SHA_DIGEST_LENGTH];
        u8 pcr17[SHA_DIGEST_LENGTH];
        memset(zeros, 0, SHA_DIGEST_LENGTH);
        
        SHA1_Init(&ctx);
        SHA1_Update(&ctx, zeros, SHA_DIGEST_LENGTH);
        SHA1_Update(&ctx, digest, SHA_DIGEST_LENGTH);
        SHA1_Final(pcr17, &ctx);

        print_hex("[AMD] Expected PCR-17: ", pcr17, SHA_DIGEST_LENGTH);
    }    
}

//---init main----------------------------------------------------------------
void cstartup(multiboot_info_t *mbi){
    module_t *mod_array;
    u32 mods_count;
    size_t sl_rt_size;
    
    //initialize debugging early on
#ifdef __DEBUG_SERIAL__        
    init_uart();
#endif

#ifdef __DEBUG_VGA__
    vgamem_clrscr();
#endif

    mod_array = (module_t*)mbi->mods_addr;
    mods_count = mbi->mods_count;

    printf("\nINIT(early): initializing, total modules=%u", mods_count);
    //ASSERT(mods_count == 2);  //runtime and OS boot sector for the time-being


    //check CPU type (Intel vs AMD)
    {
        u32 vendor_dword1, vendor_dword2, vendor_dword3;
        asm(    "xor    %%eax, %%eax \n"
                "cpuid \n"        
                "mov    %%ebx, %0 \n"
                "mov    %%edx, %1 \n"
                "mov    %%ecx, %2 \n"
                :    //no inputs
                : "m"(vendor_dword1), "m"(vendor_dword2), "m"(vendor_dword3)
                : "eax", "ebx", "ecx", "edx" );

        if(vendor_dword1 == AMD_STRING_DWORD1 && vendor_dword2 == AMD_STRING_DWORD2
           && vendor_dword3 == AMD_STRING_DWORD3)
            cpu_vendor = CPU_VENDOR_AMD;
        else if(vendor_dword1 == INTEL_STRING_DWORD1 && vendor_dword2 == INTEL_STRING_DWORD2
                && vendor_dword3 == INTEL_STRING_DWORD3)
            cpu_vendor = CPU_VENDOR_INTEL;
        else{
            printf("\nINIT(early): error(fatal), unrecognized CPU! 0x%08x:0x%08x:0x%08x",
                   vendor_dword1, vendor_dword2, vendor_dword3);
            HALT();
        }            
    }

    printf("\nINIT(early): detected an %s CPU", ((cpu_vendor == CPU_VENDOR_INTEL) ? "Intel" : "AMD"));


    //deal with MP and get CPU table
    dealwithMP();

    //find highest 2MB aligned physical memory address that the hypervisor
    //binary must be moved to
    sl_rt_size = mod_array[0].mod_end - mod_array[0].mod_start;
    hypervisor_image_baseaddress = dealwithE820(mbi, PAGE_ALIGN_UP2M((sl_rt_size))); 

    //relocate the hypervisor binary to the above calculated address
    memcpy((void*)hypervisor_image_baseaddress, (void*)mod_array[0].mod_start, sl_rt_size);
    hashandprint("INIT(early): sha1(sl+runtime): ",
                 (u8*)hypervisor_image_baseaddress, sl_rt_size);

    ASSERT(sl_rt_size > 0x20000); /* 128K */
    
    hashandprint("INIT(early): sha1(64K sl): ",
                 (u8*)hypervisor_image_baseaddress, 0x10000);
    hashandprint("INIT(early): sha1(128K sl): ",
                 (u8*)hypervisor_image_baseaddress, 0x20000);

    /* XXX TODO: Somehow ensure runtime for SL fits inside first 64K
       (that includes SL's runtime stack) */
    
    //print out stats
    printf("\nINIT(early): relocated hypervisor binary image to 0x%08x", hypervisor_image_baseaddress);
    printf("\nINIT(early): 2M aligned size = 0x%08lx", PAGE_ALIGN_UP2M((mod_array[0].mod_end - mod_array[0].mod_start)));
    printf("\nINIT(early): un-aligned size = 0x%08lx", mod_array[0].mod_end - mod_array[0].mod_start);

    //fill in "sl" parameter block
    {
        //"sl" parameter block is at hypervisor_image_baseaddress + 0x10000
        SL_PARAMETER_BLOCK *slpb = (SL_PARAMETER_BLOCK *)((u32)hypervisor_image_baseaddress + 0x10000);
        ASSERT(slpb->magic == SL_PARAMETER_BLOCK_MAGIC);
        slpb->hashSL = 0;
        slpb->errorHandler = 0;
        slpb->isEarlyInit = 1;    //this is an "early" init
        slpb->numE820Entries = grube820list_numentries;
        memcpy((void *)&slpb->e820map, (void *)&grube820list, (sizeof(GRUBE820) * grube820list_numentries));         
        slpb->numCPUEntries = pcpus_numentries;
        memcpy((void *)&slpb->pcpus, (void *)&pcpus, (sizeof(PCPU) * pcpus_numentries));
        slpb->runtime_size = (mod_array[0].mod_end - mod_array[0].mod_start) - PAGE_SIZE_2M;      
        slpb->runtime_osbootmodule_base = mod_array[1].mod_start;
        slpb->runtime_osbootmodule_size = (mod_array[1].mod_end - mod_array[1].mod_start); 
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
    ASSERT( edx == 0 ); //APIC is below 4G
  
    if(eax & 0x100)
        return 1;
    else
        return 0;
}


//---CPUs must all have their microcode cleared for SKINIT to be successful-----
void clearMicrocode(VCPU *vcpu){
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
void mp_cstartup (VCPU *vcpu){
    //sanity, we should be an Intel or AMD core
    ASSERT(vcpu->cpu_vendor == CPU_VENDOR_INTEL ||
           vcpu->cpu_vendor == CPU_VENDOR_AMD);

    if(isbsp()){
        //clear microcode if AMD CPU
        if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
            printf("\nBSP(0x%02x): Clearing microcode...", vcpu->id);
            clearMicrocode(vcpu);
            printf("\nBSP(0x%02x): Microcode clear.", vcpu->id);

            deactivate_all_localities(); /* prepare TPM for DRTM */            
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
        do_drtm(vcpu, hypervisor_image_baseaddress); // this function will not return
    
        printf("\nBSP(0x%02x): FATAL, should never be here!", vcpu->id);
        HALT();
    
    }else{
        //clear microcode if AMD CPU
        if(vcpu->cpu_vendor == CPU_VENDOR_AMD){
            printf("\nAP(0x%02x): Clearing microcode...", vcpu->id);
            clearMicrocode(vcpu);
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
