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

/* svm.c functions for handling AMD SVM extensions 
 * Written for TrustVisor by Arvind Seshadri
 */

#include <types.h>
#include <processor.h>
#include <string.h>
#include <msr.h>
#include <svm.h>
#include <error.h> 
#include <print.h>
#include <visor.h>
#include <paging.h>
#include <io.h>
#include <pci.h>
#include <dev.h>
#include <loader.h>

struct vmcb_struct *linux_vmcb; 

static void msrpm_set_write(u32 msr) __attribute__ ((section ("_init_text")));
void init_msrpm(void) __attribute__ ((section ("_init_text")));
void init_iopm(void) __attribute__ ((section ("_init_text")));

/* check and enable SVM features */
void init_svm(void)
{
  u32 eax, edx, ecx, ebx;

  /* check if CPU supports SVM extensions */
  cpuid(0x80000001, &eax, &ebx, &ecx, &edx);
  if( !(ecx & (1<<ECX_SVM)) ){
    EARLY_FAIL();
  }
  
  /* check if SVM extensions are disabled by the BIOS */
  rdmsr(MSR_VM_CR, &eax, &edx);
  if( eax & (1<<VM_CR_SVME_DISABLE) ){
    EARLY_FAIL();
  }

  /* check for nested paging support and number of ASIDs */
  cpuid(0x8000000a, &eax, &ebx, &ecx, &edx); 
  if( !(edx & (1<<EDX_NP)) ){
    EARLY_FAIL();
  }

  /* enable SVM and debugging support (if required) */  
  DEBUG{
    rdmsr((u32)MSR_VM_CR, &eax, &edx);
    eax &= (~(1 << VM_CR_DPD));
    wrmsr((u32)MSR_VM_CR, eax, edx);
  }
  rdmsr((u32)MSR_EFER, &eax, &edx);
  eax |= (1 << EFER_SVME);
  wrmsr((u32)MSR_EFER, eax, edx);

  return;
}

/* setup hsave area after relocating TrustVisor */
void init_svm_post(void)
{
  u64 hsave_pa;
  u32 eax, edx;
  extern u32 visor_hsave_area[];

  /* Initialize the HSA */
  hsave_pa = (u64)__pa((u32)visor_hsave_area);
  eax = (u32)hsave_pa;
  edx = (u32)(hsave_pa >> 32);
  wrmsr((u32)MSR_HSAVE_PA, eax, edx);
  
  printf("INFO: SVM HSA set up\n");

  return;
}

/* help function to setup msr permission vector */
static void msrpm_set_write(u32 msr)
{
  extern u8 visor_msr_perm_bitmap[];
  u32 byte_offset, bit_offset;

  if ((msr >= (u32)0xC0000000) && (msr < (u32)0xC0002000))
    msr = (msr - (u32)0xC0000000) + 0x2000;
  else if ((msr >= (u32)0xC0010000) && (msr < (u32)0xC0012000))
    msr = (msr - (u32)0xC0010000) + 0x4000;
  
  /* each msr cover 2 bits, one for read and one for write */
  byte_offset = (msr << 1) / 8;
  bit_offset = (msr << 1) & 7;
  visor_msr_perm_bitmap[byte_offset] |= (1 << (bit_offset + 1));
}

/* msr permission vector initialization */
void init_msrpm(void)
{
  extern u8 visor_msr_perm_bitmap[];

  msrpm_set_write(MSR_VM_CR);
  msrpm_set_write(MSR_IGNNE);
  msrpm_set_write(MSR_SMM_CTL);
  msrpm_set_write(MSR_HSAVE_PA);

  linux_vmcb->msrpm_base_pa = __pa((u32)visor_msr_perm_bitmap);

  printf("INFO: SVM msr permission bitmap initialized\n");
}

/* io permission vector initialization */
void init_iopm(void)
{
  extern u8 visor_io_perm_bitmap[];
  /* we only intercept data port access because we can get the 
   * address information from address port 
   */
  iopm_set_write(CONFIG_DATA_PORT, 4);
  linux_vmcb->iopm_base_pa = __pa((u32)visor_io_perm_bitmap);

  printf("INFO: SVM io permission bitmap initialized\n");
}

/* initialize vmcb for main Linux kernel booting */
void init_linux_vmcb(void)
{
  extern u32 visor_vmcb_label[];
  
  linux_vmcb = (struct vmcb_struct *)visor_vmcb_label;
  
  /* set up cpu state for booting linux:
   * protected mode with
   * cs = 0x0010
   * ds = es = ss = 0x0018
   * fs and gs keep the value for real mode 
   * fs = gs = 0x1000
   * cli() =  cli
   */
  /* Linux main kernel starts execution in protected mode (cpl 0) */

  /* initialize segment descriptors for protected mode execution */

  /* set up CS descr */
  linux_vmcb->cs.sel = 0x1020;
  linux_vmcb->cs.base = 0x10200;
  linux_vmcb->cs.limit = 0xffff;
  linux_vmcb->cs.attr.bytes = 0x009e;
  
  /* set up DS descr */
  linux_vmcb->ds.sel = 0x1000;
  linux_vmcb->ds.base = 0x100000;
  linux_vmcb->ds.limit = 0xffff;
  linux_vmcb->ds.attr.bytes = 0x0092;
  
  /* set up ES descr */
  linux_vmcb->es.sel = 0x1000;
  linux_vmcb->es.base = 0x10000;
  linux_vmcb->es.limit = 0xffff;
  linux_vmcb->es.attr.bytes = 0x0093;

  /* set up FS descr */
  linux_vmcb->fs.sel = 0x1000;
  linux_vmcb->fs.base = 0x10000;
  linux_vmcb->fs.limit = 0xffff; 	/* keep settings in real mode */
  linux_vmcb->fs.attr.bytes = 0x0093;

  /* set up GS descr */
  linux_vmcb->gs.sel = 0x1000;
  linux_vmcb->gs.base = 0x10000;
  linux_vmcb->gs.limit = 0xffff; 	/* keep settings in real mode */
  linux_vmcb->gs.attr.bytes = 0x0093;

  /* set up SS descr */
  linux_vmcb->ss.sel = 0x1000;
  linux_vmcb->ss.base = 0x10000;
  linux_vmcb->ss.limit = 0xffff;
  linux_vmcb->ss.attr.bytes = 0x0093;

  /* set up idtr descr */
  linux_vmcb->idtr.sel = 0;
  linux_vmcb->idtr.base = 0;
  linux_vmcb->idtr.limit = 0xffff;
  linux_vmcb->idtr.attr.bytes = 0x0082;

  /* SVME needs to be set in EFER for vmrun to execute */
  linux_vmcb->efer = (1 << EFER_SVME);

  /* initialize sp, Linux kernel doesn't reply on this value */
  linux_vmcb->rsp = LINUX_BOOT_SP;
  
  linux_vmcb->rflags = 0;
  linux_vmcb->guest_asid = 1; 	/* ASID 0 reserved for host */
  linux_vmcb->cpl = 0; /* set cpl to 0 for real mode */

  /* set guest PAT to state at reset. Linux does not use PAT.
   * checked this using the hdt while the kernel is running.
   * PAT value is same as that set by CPU at reset
   */
  linux_vmcb->g_pat = 0x0007040600070406ULL;

  /* set state of control regs and debug regs. the state was
   * obtained using the HDT to observe the CPU state before
   * Linux boot strap code calls the Linux main kernel
   */
  linux_vmcb->cr0 = CR0_ET; 	/* Extension Type enabled */
  linux_vmcb->cr2 = linux_vmcb->cr3 = linux_vmcb->cr4 = 0ULL;

  linux_vmcb->dr6 = 0ULL;
  linux_vmcb->dr7 = 0ULL;
 
  linux_vmcb->dr_intercepts = 0;

  linux_vmcb->cr_intercepts = 0;
  linux_vmcb->exception_intercepts = 0;
  linux_vmcb->general1_intercepts = 0;
  linux_vmcb->general1_intercepts |= (u32)GENERAL1_INTERCEPT_MSR_PROT;
  /* we only intercept io port access to protect DEV configuration */
  linux_vmcb->general1_intercepts |= (u32)GENERAL1_INTERCEPT_IOIO_PROT;

  /* intercept all SVM instructions */
  linux_vmcb->general2_intercepts |= (u32)(GENERAL2_INTERCEPT_VMRUN |
					  GENERAL2_INTERCEPT_VMMCALL |
					  GENERAL2_INTERCEPT_VMLOAD |
					  GENERAL2_INTERCEPT_VMSAVE |
					  GENERAL2_INTERCEPT_STGI |
					  GENERAL2_INTERCEPT_CLGI |
					  GENERAL2_INTERCEPT_SKINIT |
					  GENERAL2_INTERCEPT_ICEBP);
  /* set up msr intercepts. */
  init_msrpm();

  /* set up I/O intecepts to prevent writes to PCI config space */
  init_iopm();

  /* set up IP for Linux kernel */
  linux_vmcb->rip = 0;
  
  return;
}
