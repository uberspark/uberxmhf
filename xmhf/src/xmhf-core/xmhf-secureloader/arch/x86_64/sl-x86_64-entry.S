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

/* EMHF secure loader component entry point
  authors: amit vasudevan (amitvasudevan@acm.org) and jonmccune@cmu.edu
*/

#include <xmhf.h>

/*----------------------------------------------------------------------
 CODE
----------------------------------------------------------------------

our C main*/

.extern xmhf_sl_main

/* The first 3 pages of the SL serve different purposes depending on
   whether the system has an AMD or Intel CPU.  On an AMD system, the
   first four bytes of the first page comprise the SLB Header.  The
   remainder goes to waste (3*4K-4B).

   On Intel, these first three pages are used as the MLE Page Tables.
   These are constructed in software with the txt.c:build_mle_pagetable()
   function.  The AMD header will be clobbered in the process.

   These 3 pages are placed at the very beginning of the SL (byte 0)
   by our linker script.  Our SL is always padded to 64K in size
   regardless of the actual size of the code or data.  The linker
   relocation base for our SL is always 0.  The SL must be position-
   independent. */

.section .sl_header, "aw"
    .global _mle_page_table_start
    _mle_page_table_start:

    .global _sl_header
    _sl_header:         /* AMD-specific header format for Secure Loader Block (SLB). */
    .word _sl_start     /* SL entry point relative to header (bits 0-15).*/
    .word 0xFFFF         /*SL size including the header (bits 16-32),*/
                         /*i.e, 0 through 65535 inclusive = 64K */


    /* Three 4K pages to hold the "MLE page tables" for an Intel-specific
     DRTM using GETSEC[SENTER].  See 2.2.4.1 in Intel MLE
     Developer's Guide (Dec. 2009 revision).*/
    .align 4096      // remainder of first page

    .global g_sl_protected_dmabuffer
    g_sl_protected_dmabuffer:
    .fill 4096, 1, 0 /* second page*/
    .fill 4096, 1, 0 /* third page*/
    .global _mle_page_table_end
    _mle_page_table_end:


.section .text
    /* Make room for MLE header at beginning*/
    .global _mle_hdr
    _mle_hdr:
    .fill TEMPORARY_MAX_MLE_HEADER_SIZE, 1, 0x90 /* XXX TODO just a guess; should really be sizeof(mle_hdr_t) */

    .global _sl_start
    _sl_start:

    .code32

    /* get (physical location of secure loader - link location) in EBP */
    call 1f
1:  popl %ebp // put EIP into EAX
    subl $1b, %ebp

    /* XXX require EBP to be 2M-aligned, or page table will mis-align */
    movl $0x1fffff, %eax
    testl %ebp, %eax
    je 5f
6:  hlt
    jmp 6b
5:

    /* load 64-bit GDT */
    addl %ebp, sl_gdt_ptr(%ebp)
    lgdt sl_gdt(%ebp)

    /* set CR4 (enable PAE) */
    movl %cr4, %eax
    orl $(CR4_PAE), %eax
    movl %eax, %cr4

    /* set up identity-map page table */

    /* clear memory */
    leal sl_long_pt_begin(%ebp), %eax
    leal sl_long_pt_end(%ebp), %ebx
2:  cmpl %eax, %ebx
    jbe 3f
    movl $0, (%eax)
    addl $4, %eax
    jmp 2b
3:

    /* set PML4T (1 entry, 512 GiB per entry) */
    leal sl_pdpt(%ebp), %eax
    orl $0x3, %eax              /* set P and R/W bits */
    movl %eax, sl_pml4t(%ebp)   /* store PML4T[0] */

    /* set PDPT (1 entry, 1 GiB per entry) */
    leal sl_pdt(%ebp), %eax
    orl $0x3, %eax              /* set P and R/W bits */
    movl %eax, sl_pdpt(%ebp)    /* store PDPT[0] */

    /* set PDT (512 entries, 2 MiB per entry) */
    movl $0, %eax
    movl $512, %ecx
4:  movl %eax, %ebx
    shll $21, %ebx
    orl $0x83, %ebx
    movl %ebx, sl_pdt(%ebp, %eax, 8)    /* store PDT[EAX] */
    incl %eax
    cmpl %eax, %ecx
    ja 4b

    /* set CR3 (location of PML4T) */
    leal sl_pml4t(%ebp), %eax
    movl %eax, %cr3

    /* set EFER MSR LME */
    movl $(MSR_EFER), %ecx
    rdmsr
    btsl $(EFER_LME), %eax
    wrmsr

    /* set LDT and TSS (from Linux code) */
    xorl %eax, %eax
    lldt %ax
    movl $0x20, %eax    /* 4th entry in GDT (TSS) */
    ltr %ax

    /* setup jump to 64-bit mode */
    pushl $0x10         /* 2nd entry in GDT (64-bit CODE) */
    leal _sl_start_64(%ebp), %eax
    pushl %eax

    /* enable paging */
    movl %cr0, %eax
    orl $(CR0_PG), %eax
    movl %eax, %cr0

    /* jump to 64-bit mode */
    lret

    .code64

    _sl_start_64:

    /*
     * Modify the page table so that VA + RBP = PA.
     * There is PA = RBP + link time address, so VA = link time address.
     * In x86 mode this was implemented using GDT. Now we use page table.
     * Assumption 1: SL is less than a page (2 MiB)
     * Assu
     */

    /* calculate RBP (was EBP) again */

    leaq (%rip), %rbp
1:  subq $1b, %rbp

    /* we need RBP to be 2M-aligned */
    movq $0x1fffff, %rax
    testq %rbp, %rax
    je 3f
2:  hlt
    jmp 2b
3:

    /* check RBP == 0 */
    testq %rbp, %rbp
    jz _sl_skip_page_table_change   /* unlikely to jump */

    /* change PDT[0] */
    movq %rbp, %rbx
    orq $0x83, %rbx
    movq %rbx, sl_pdt(%ebp)         /* store PDT[0] */

    /* jump to virtual page 0 */
    movq $4f, %rax                  /* RAX now has link time address */
    jmpq *%rax
4:

    /* set PDT[1:] (511 entries, 2 MiB per entry) */
    movq $1, %rax
    movq $512, %rcx
5:  movq %rax, %rbx
    shlq $21, %rbx
    addq %rbp, %rbx
    orq $0x83, %rbx
    movq %rbx, sl_pdt(%rbp, %rax, 8)    /* store PDT[EAX] */
    incq %rax
    cmpq %rax, %rcx
    ja 5b

    _sl_skip_page_table_change:

    /* Now we only need RBP */
    xorq %rax, %rax
    xorq %rbx, %rbx
    xorq %rcx, %rcx
    xorq %rdx, %rdx

    /* Setup ESP to top of 64K (it will already be there on AMD)*/
    movl $0x10000, %esp /* XXX TODO Get rid of magic number*/

#ifndef PERF_CRIT
    /*get cycle count using rdtsc; useful to evaluate how long DRTM
    takes*/
    cpuid /*Serializing instruction; causes more overhead :(*/
    rdtsc
    pushq %rdx
    pushq %rax
#endif

    /* Determine processor type to perform some low-level initialization
     after DRTM. On AMD CPUs, we need to clear R_INIT, DIS_A20M and
     CR_DPD (to enable HDT access) in VM_CR_MSR.*/
sl_cpu_vendor:
    xor    %eax, %eax
    cpuid
    cmpl $(INTEL_STRING_DWORD1), %ebx
    jne sl_cpu_vendor_notintel
    cmpl $(INTEL_STRING_DWORD2), %edx
    jne sl_cpu_vendor_notintel
    cmpl $(INTEL_STRING_DWORD3), %ecx
    jne sl_cpu_vendor_notintel
    movl $(CPU_VENDOR_INTEL), %esi
    jmp sl_cpu_intel
sl_cpu_vendor_notintel:
    cmpl $(AMD_STRING_DWORD1), %ebx
    jne sl_cpu_vendor_unknown
    cmpl $(AMD_STRING_DWORD2), %edx
    jne sl_cpu_vendor_unknown
    cmpl $(AMD_STRING_DWORD3), %ecx
    jne sl_cpu_vendor_unknown
    movl $(CPU_VENDOR_AMD), %esi
    jmp sl_cpu_amd
sl_cpu_vendor_unknown:
    //this should never happen, but we have a fallback in case
    ud2
    hlt

    /* If AMD CPU enable a few things that SKINIT disables.
     Enable HDT debugging, also clear R_INIT and DIS_A20M.
    XXX TODO Disable HDT debugging; represents a security vulnerability*/
sl_cpu_amd:
    movl $(VM_CR_MSR), %ecx
    rdmsr
    andl $(~(1<<VM_CR_DPD)), %eax
    andl $(~(1<<VM_CR_R_INIT)), %eax
    andl $(~(1<<VM_CR_DIS_A20M)), %eax
    wrmsr

    movq $(CPU_VENDOR_AMD), %rdx
    jmp sl_cpu_common

sl_cpu_intel:
    movq $(CPU_VENDOR_INTEL), %rdx
    jmp sl_cpu_common

    /* Common code from now on*/
sl_cpu_common:

    /* In x86 GDT is modified, but not here */

    /* cpu vendor is in rdx, move it into rdi */
    movq %rdx, %rdi

#ifndef PERF_CRIT
    // push measurements onto the new stack
    popq %rdx           /* 4th argument: EDX of cpuid */
    popq %rcx           /* 3rd argument: EAX of cpuid */
#else
    movq $0, %rdx       /* 4th argument */
    movq $0, %rcx       /* 3rd argument */
#endif

    movq %rbp, %rsi     /* 2nd argument */
    /* 1st argument: vendor, already in RDI */

    call xmhf_sl_main   /*call SL main routine*/

    /* We should never get here*/
    spinforever:
        jmp spinforever
    hlt

/*----------------------------------------------------------------------
 DATA
----------------------------------------------------------------------*/

.section .data

    //the secure loader GDT
    sl_gdt:
    .word    sl_gdt_end - sl_gdt_start         // XXX WAS PREVIOUSLY +-1 !!!
    sl_gdt_ptr:
    .long    sl_gdt_start                      // This will be fixed up to sl load-base
    .align   16
    sl_gdt_start:
    .quad    0x0000000000000000                //0x00: NULL selector
    .quad    0x00cf9a000000ffff                //0x08: 32-bit CODE selector
    .quad    0x00af9a000000ffff                //0x10: 64-bit CODE selector
    .quad    0x00cf92000000ffff                //0x18: 32-bit DATA selector
    .quad    0x0080890000000000                //0x20: TSS (from Linux)
    .quad    0x0000000000000000                //0x28: NULL selector
    sl_gdt_end:


/*----------------------------------------------------------------------
 STACK
----------------------------------------------------------------------*/

/* sl stack, this is just a placeholder and ensures that the linker
 actually "allocates" the stack up until 0x10000*/
.section .sl_stack
    .fill 2048, 1, 0

/*----------------------------------------------------------------------
 PAGE TABLE
----------------------------------------------------------------------*/

/* page table for long mode */
.section .sl_long_pt
    sl_long_pt_begin:
    sl_pml4t:
    .fill 4096, 1, 0
    sl_pdpt:
    .fill 4096, 1, 0
    sl_pdt:
    .fill 4096, 1, 0
    sl_long_pt_end:
