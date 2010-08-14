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

/* visor.c: TrustVisor initialization code 
 * Written for TrustVisor by Arvind Seshadri and Ning Qu
 */

#include <types.h>
#include <multiboot.h>
#include <string.h>
#include <processor.h>
#include <print.h>
#include <error.h>
#include <svm.h>
#include <sha1.h>
#include <prot.h>
#include <visor.h>
#include <paging.h>
#include <heap.h>
#include <msr.h>
#include <io.h>
#include <pci.h>
#include <dev.h>
#include <tpm.h>
#include <scode.h>
#include <ucode.h>
#include <malloc.h> // for static_malloc_init
#include <timer.h>  // for performance number
/* for debugging */
u32 debug_flag = 1;

unsigned long mmu_cr4_features;
u32 visor_relocate_address;
u32 is_relocated = 0;
u32 relocated_visor_vmcb;
u32 max_pfn __attribute__ ((section ("_init_data")));
hashlist_entry_t visor_checksum[1] __attribute__ ((section ("_init_data"))) = {
#include "hashvisor.c"
};

interrupt_gate_descriptor_t idt_table[256] __attribute__ \
((section ("visor_idt") aligned (4)));
pseudo_descriptor_t idt_descr __attribute__ \
((section ("visor_idt") aligned (4)));
extern u32 startup_stack[];

void init_idt(void) __attribute__ ((section ("_init_text")));
void init_visor(void) __attribute__ ((section ("_init_text")));
void init_visor_post(void) __attribute__ ((section ("_init_text")));
void check_stack(void) __attribute__ ((section ("_init_text")));
void enable_paging(u32 reladdr) __attribute__ ((section ("_init_text")));
u32 activate_kernel(void) __attribute__ ((section ("_init_text")));
u32 visor_verify_binary(void) __attribute__ ((section ("_init_text")));

u32 initsec_tpm(void) __attribute__ ((section ("_init_text")));

void measure_ucode(u32 ucode_addr);
void init_dev_boot(void);
void find_dev(void);
void init_dev_rt1(void);
void init_dev_rt2(void);
void remove_dev_boot(void);

/* help macro to access the parameters on the stack passed by Loader */
#define GET_INIT_PARAMS(index)\
  (*(u32 *)((u32)&startup_stack + STARTUP_STACK_SIZE - 4 * (index)))

/* initialize TrustVisor before enabling paging */
void init_visor(void)
{
  /* NOTE, NOTE, NOTE: DO NOT declare this as "extern u32
   * *visor_pdp_table". For some reason, this makes gcc generate code
   * that dereferences "visor_pdp_table" when you refer to it as
   * "visor_pdp_table" in your code.
   */
  extern u32 visor_pdp_table[];
  u32 eax, ebx, ecx, edx;
  unsigned long cr0, cr3;
  unsigned long ucode_addr;
  int tpm;
  
  /* At this point only the first 64KB of TrustVisor (the SLB) is
   * protected from DMA reads and writes. Until we set up a bit vector
   * to protect other areas of TrustVisor, we need to make sure that 
   * all resources used (both code and data) lie within the first 64KB.
   */

  /* Do some sanity checks before initializing SVM and DEV */
  /* check if AMD CPU */
  cpuid(0x00, &eax, &ebx, &ecx, &edx);
  if( (ebx != AMD_STRING_DWORD1) || (ecx != AMD_STRING_DWORD2) ||
      (edx != AMD_STRING_DWORD3) )
    EARLY_FAIL();

  /* check if CPU supports PAE */
  cpuid(0x1, &eax, &ebx, &ecx, &edx);
  if( !(edx & (1 << EDX_PAE)) )
    EARLY_FAIL();

  /* check for NX support */
  cpuid(0x80000000, &eax, &ebx, &ecx, &edx);
  if( eax <= 0x80000000 )
    EARLY_FAIL();

  cpuid(0x80000001, &eax, &ebx, &ecx, &edx);
  if( !(edx & (1 << EDX_NX)) )
    EARLY_FAIL();

  /* zero out the init bss 
   * note: before runtime area is verified, we don't rely on any functions
   *       in it, such as memset
   */
  init_memset((void*)_visor_init_edata, 0, (u32)((u32)startup_stack - (u32)_visor_init_edata));

  /* Set up initial DEV protections. This should protect the first 64MB 
   * of memory from DMA reads and writes .
   */
  /* check for DEV support */
  find_dev(); 

  init_dev_boot();
  DEBUG printf("DEBUG: initsec prepare tpm\n");
  tpm = initsec_prepare_tpm();
  /* hash runtime and extend into some pcr. note this __must__ be done
   * after init dev protected memory setup and before we wan to access
   * anything in the runtime area to avoid tocttou vulnerability.
   */
  if (!visor_verify_binary())
    EARLY_FAIL();

  /* Now initialize SVM. */ 
  init_svm();

  /* Initialize display. This is done after setting up DEV protections 
   * so that global variable used by the video driver are protected 
   * from DMA writes 
   */
#ifdef __USE_SERIAL__
  init_uart();
#else
  init_vga();
#endif
  printf("INFO: Initialized display\n");

#if 0
  printf("Early TPM init returned id->did_vid %d. Now doing Runtime TPM init.\n", tpm);
  init_tpm();
#endif      
  /* zero out the runtime bss 
   * note: we can't do this too late, maybe some function already relies
   * on the value in bss segment 
   */
  memset((void*)_visor_bss_start, 0, (u32)_visor_bss_end - (u32)_visor_bss_start);

  /* this parameter on the stack is passed by Loader */
  max_pfn = GET_INIT_PARAMS(1);

  printf("INFO: Maximum page number is 0x%08lx\n", (unsigned long)max_pfn);
#define MAX_PFN_DEFAULT 	0x000C0000
  if (max_pfn >= 0x100000)
  {
    printf("    : Maximum page number is over 4GB address space, current system assume the memory in 32 bit addres space\n");
    printf("    : Maximum page number is changed 0x%08lx ==> 0x%08lx\n", (unsigned long)max_pfn, (unsigned long)MAX_PFN_DEFAULT);
    max_pfn = MAX_PFN_DEFAULT;
  }

  /* Apply microcode patch to CPU */
  ucode_addr = GET_INIT_PARAMS(2);
  if(ucode_addr) {
      printf("INFO: Found microcode patch at address 0x%08lx\n", ucode_addr);
      //dump_bytes((u8*)ucode_addr, 32);
      measure_ucode(ucode_addr);
      core_load_ucode(ucode_addr);
  } else {
      printf("INFO: No microcode patch found. Continuing anyways.\n");
  }
  
  /* Calculate highest 32MB aligned address to relocate TrustVisor to */
  visor_relocate_address = ((max_pfn << PAGE_SHIFT_4K) & ~((u32)VISOR_RUNTIME_SIZE - 1)) 
                            - (VISOR_RUNTIME_SIZE);
  printf("INFO: Visor is relocated to address 0x%08lx\n", (unsigned long)visor_relocate_address);

  /* Initialize DEV before relocating TrustVisor */
  init_dev_rt1();

  /* relocate visor runtime to top of ram */
  is_relocated = 1;  
  memcpy((void*)visor_relocate_address, (void*)VISOR_RUNTIME_START, (u32)VISOR_RUNTIME_SIZE);

  /* Initialize DEV after relocating TrustVisor */
  init_dev_rt2();
  
  check_stack();
   
  /* set up page table for TrustVisor */
  init_visor_pt();

  /* enable NX protections */
  rdmsr(MSR_EFER, &eax, &edx);
  eax |= (1 << EFER_NXE);
  wrmsr(MSR_EFER, eax, edx);
  
  /* Set up CR4, except global flag which Intel requires should be
   * left until after paging is enabled (IA32 Manual Vol. 3, Sec. 2.5)
   */
  mmu_cr4_features = CR4_PAE;
  write_cr4(mmu_cr4_features);
  
  /* Set up cr0. Note on EM bit. Setting EM bit causes the CPU to act
   * as if it did not have a floating point unit. Thus, an attempt to
   * execute any FP, MMX, or SSE instruction causes the CPU to
   * generate an exception. This behavior is desirable in the TrustVisor
   * since we do not use any FP, MMX, or SSE instructions.
   */
  cr0 = (unsigned long)0x00000015; /* ET, EM, PE. enable PG later */
  write_cr0(cr0);

  /* set up cr3 before we enable paging */
  cr3 = __pa((u32)visor_pdp_table);
  write_cr3(cr3);

  /* after this function returns, we will enable paging and switch 
   * to runtime stack. And then we will call init_visor_post which 
   * continues other initialization in protected mode
   */
}

/* this function runs based on runtime stack with paging enabled */
void init_visor_post(void)
{
  extern u32 visor_vmcb_label[];
  u32 cr4;
  per_timer timer_genkey;
  sha1_context ctx;
  u8 sha1sum[SHA1_CHECKSUM_LEN];

  //#define RSA_KEY_GEN_PER
#ifdef RSA_KEY_GEN_PER
  int inum;
  int exp_num = 100;
  int time_buf[100];
  int time_sum = 0;
  per_timer keygen_per_timer;
  
#endif
  /* Paging enabled, now set the global flag */
  
  /* Note on setting cr4 global-enable: AMD SVM extensions support ASIDs whereby 
   * each address space can be assigned a unique ASID by the hypervisor. This 
   * eliminates the need to flush the TLB on an address space switch since the 
   * TLB entries are tagged with ASIDs. However, TLB flush operations, move to 
   * cr4 and move to cr3, behave identically whether or not SVM extensions are 
   * enabled: move to cr3 flushes the non-global TLB entries across all ASIDs 
   * while move to cr4 flushes all TLB entries. Therefore, it is necessary to 
   * set the G bit in TrustVisor's page table entires so that these entries are not 
   * flushed whenever the OS schedules a new process (move to cr3).
   */
  cr4 = read_cr4();
  cr4 |= CR4_PGE;
  write_cr4(cr4);

  /* Now that the runtime memory is DEV protected, the runtime is
   * relocated, and paging is enabled, it is safe and correct to write
   * to the runtime memory.
   */

  /* Initialise IDT with simple error defaults. */
  init_idt();

  /* Initialize heap */
  init_heap();

  /* Initialize SVM extensions */
  init_svm_post();

  /* Set up vmcb for booting Linux */
  init_linux_vmcb();
  printf("INFO: Linux bootstrap environment initialized ....\n");

  /* Initialize scode whitelist for verification */
  init_scode();

  /* Initialize TPM */
#if 1 /* Need to do this a lot sooner. -Jon */
  init_tpm();
#endif

  /* Initialize nested page table for guest address space */
  init_nested_paging();
  activate_nested_paging();

  /* Get relocated physical address of the vmcb */
  relocated_visor_vmcb = __pa((u32)visor_vmcb_label);

  remove_dev_boot();


  static_malloc_init();

#ifdef RSA_KEY_GEN_PER
  for (inum = 0; inum < exp_num; inum++)
  {
    time_start(&keygen_per_timer);
    rsa_gen_key(&g_rsa, 2048, 65537);
    time_stop(&keygen_per_timer);
    time_buf[inum] = diff_timing(&keygen_per_timer);
    rsa_free(&g_rsa);
  }
  
  printf("Performace: 2048 bits RSA Key Gen Performace, %d times\n", exp_num);
  for (inum = 0; inum < exp_num; inum++)
  {
    time_sum += time_buf[inum];
    printf("Performance: 2048 bits RSA Key Gen Perf, the %d (th) Key Pair, %d (ms)\n", (inum+1), time_buf[inum]);
  }

  printf("Performace: 2048 bits RSA Key Gen Perf, Average of %d times, %d (ms)\n", exp_num, time_sum/exp_num);
  
#endif

  time_start(&timer_genkey);
  rsa_gen_key(&g_rsa, 2048, 65537);
  time_stop(&timer_genkey);
  printf("Performance: TrustVisor Generate 2048 bits RSA Key pair, time %d (ms)\n", diff_timing(&timer_genkey));
  printf("Create RSA Key Complete\n");

#if 1
  // Extend Pcr 18 with public key
  init_sha1_starts(&ctx);
  init_sha1_update(&ctx, (u8 *)g_rsa.N.p, 2048);
  init_sha1_finish(&ctx, sha1sum);

  DEBUG printf("initsec TPM extend\n");
  initsec_TPM_Extend(18, sha1sum);

#endif
  tpm_deactive();
  DEBUG printf("DEBUG: CPU CR3 value is %#lx\n", read_cr3());
  printf("INFO: Now booting Linux....\n");
}

/* default interrupt (exception) handler */
void ignore_int(void)
{
  printf("FATAL ERROR: Unknown interrupt\n");
  EARLY_FAIL();
}

/* initialize interrupt vector for TrustVisor */
void init_idt(void)
{
  interrupt_gate_descriptor_t idt_entry;
  u32 i;

  /* construct an interrupt gate for the ignore_int handler. */
  idt_entry.fields.offset0 = (u16)((u32)ignore_int & 0xffff);
  idt_entry.fields.selector = __VISOR_CS;
  idt_entry.fields.resvd0 = 0;
  idt_entry.fields.type = 0xe; 
  idt_entry.fields.s = 0;
  idt_entry.fields.dpl = 3;
  idt_entry.fields.p = 1;
  idt_entry.fields.offset16 = (u16)((((u32)ignore_int) >> 16) & 0xffff);

  /* fill in all 256 entries of the IDT using the interrupt gate */
  for (i = 0; i < 256; i ++)
    idt_table[i] = idt_entry;

  /* initialize pseudo descriptor and load into idtr */
  idt_descr.limit = 256 * 8 - 1;
  idt_descr.base = (u32)idt_table;
  load_idtr((u32)&idt_descr);
}

/* Check if stack is aligned correctly */
void check_stack(void)
{
  extern u32 stack[];
  
  if (((u32)stack & (STACK_SIZE - 1)) != 0){
      printf("FATAL ERROR: Misaligned runtime stack\n");
      EARLY_FAIL();
  }

  return;
}

void measure_ucode(u32 ucode_addr) {
  u8 sha1sum[SHA1_CHECKSUM_LEN];
  u8 buffer[TCG_BUFFER_SIZE];
  sha1_context ctx;
  int rv;

  u32 ucode_size = *((u32*)ucode_addr);

/*   printf("Dump of microcode argument:\n"); */
/*   dump_bytes((u8*)ucode_addr, ucode_size + 4); */

  init_sha1_starts(&ctx);
  init_sha1_update(&ctx, (u8 *)(ucode_addr+4), ucode_size);
  init_sha1_finish(&ctx, sha1sum);

  printf("DEBUG: init_sha1(%d bytes of microcode):\n", ucode_size);
  dump_bytes(sha1sum, SHA1_CHECKSUM_LEN);
  
  rv = slb_TPM_Extend(buffer, 18, sha1sum);
  if(rv != TPM_SUCCESS) {
      printf("slb_TPM_Extend FAILED with error code %d\n", rv);
  }
}

/* generate the hash value of TrustVisor's runtime image and compare it with 
 * the preloaded hash value */
u32 visor_verify_binary(void) 
{
  sha1_context ctx;
  u8 sha1sum[SHA1_CHECKSUM_LEN];

  init_sha1_starts(&ctx);
  init_sha1_update(&ctx, (u8 *)_visor_text, (u32)_visor_data_end - (u32)_visor_text);
  init_sha1_finish(&ctx, sha1sum);

  if (init_memcmp(visor_checksum[0].checksum, sha1sum, SHA1_CHECKSUM_LEN) != 0)
      return 0;

/*   /\* To debug PCR-18, try to extend with sha1("nothing") *\/ */
/*   init_sha1_starts(&ctx); */
/*   init_sha1_finish(&ctx, sha1sum); */
  //DEBUG printf("initsec TPM extend\n");
  //initsec_TPM_Extend(18, sha1sum);
  return 1;
}

/* some help functions to setup bit vector */
void set_prot(u32 pa, u32 size, u8 *bit_vector)
{
  u32 start_pfn, end_pfn, i, j;

  start_pfn = pa >> PAGE_SHIFT_4K;
  end_pfn = PAGE_ALIGN_UP4K(pa + size) >> PAGE_SHIFT_4K;

  if ((start_pfn & 0x7) != 0)
  {
    j = (start_pfn + 0x7) & (u32)~0x7;
    for (i = start_pfn; (i < end_pfn) && (i < j); i ++)
      set_page_prot(i, bit_vector);
    start_pfn = j;
  }

  if (start_pfn < end_pfn)
  {
    j = end_pfn & (u32)~0x7;
    for (i = (start_pfn / 8); i < (j / 8); i ++)
      bit_vector[i] = 0xff;
    start_pfn = j;
  }

  if (start_pfn < end_pfn)
  {
    for (i = start_pfn; i < end_pfn; i ++)
      set_page_prot(i, bit_vector);
  }
}

void clear_prot(u32 pa, u32 size, u8 *bit_vector)
{
  u32 start_pfn, end_pfn, i, j;

  start_pfn = pa >> 12;
  end_pfn = PAGE_ALIGN_UP4K(pa + size) >> 12;

  if ((start_pfn & 0x7) != 0)
  {
    j = (start_pfn + 0x7) & (u32)~0x7;
    for (i = start_pfn; (i < end_pfn) && (i < j); i ++)
      clear_page_prot(i, bit_vector);
    start_pfn = j;
  }

  if (start_pfn < end_pfn)
  {
    j = end_pfn & (u32)~0x7;
    for (i = (start_pfn / 8); i < (end_pfn / 8); i ++)
      bit_vector[i] = 0;
    start_pfn = j;
  }

  if (start_pfn < end_pfn)
  {
    for (i = start_pfn; i < end_pfn; i ++)
      clear_page_prot(i, bit_vector);
  }
  return;
}

u32 test_prot(u32 pa, u32 size, u8 *bit_vector)
{
  u32 start_pfn, end_pfn, i, j;

  start_pfn = pa >> 12;
  end_pfn = PAGE_ALIGN_UP4K(pa + size) >> 12;

  if ((start_pfn & 0x7) != 0)
  {
    j = (start_pfn + 0x7) & (u32)~0x7;
    for (i = start_pfn; (i < end_pfn) && (i < j); i ++)
      if (test_page_prot(i, bit_vector))
        return 1;
    start_pfn = j;
  }

  if (start_pfn < end_pfn)
  {
    j = end_pfn & (u32)~0x7;
    for (i = (start_pfn / 8); i < (j / 8); i ++)
      if (bit_vector[i] != 0)
        return 1;
    start_pfn = j;
  }

  if (start_pfn < end_pfn)
  {
    for (i = start_pfn; i < end_pfn; i ++)
      if (test_page_prot(i, bit_vector))
        return 1;
  }
  return 0;
}
