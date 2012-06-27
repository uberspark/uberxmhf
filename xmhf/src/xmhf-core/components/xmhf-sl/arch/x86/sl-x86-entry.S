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

// EMHF secure loader component entry point
// authors: amit vasudevan (amitvasudevan@acm.org) and jonmccune@cmu.edu

#include <xmhf.h> 

//----------------------------------------------------------------------
// CODE
//----------------------------------------------------------------------

//our C main
.extern emhf_sl_main

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
    _sl_header:         // AMD-specific header format for Secure Loader Block (SLB).
    .word _sl_start     // SL entry point relative to header (bits 0-15).
    .word 0xFFFF        // SL size including the header (bits 16-32),
                        // i.e, 0 through 65535 inclusive = 64K


    // Three 4K pages to hold the "MLE page tables" for an Intel-specific
    // DRTM using GETSEC[SENTER].  See 2.2.4.1 in Intel MLE
    // Developer's Guide (Dec. 2009 revision).
    .align 4096      // remainder of first page
    
    .global g_sl_protected_dmabuffer
    g_sl_protected_dmabuffer:
	.fill 4096, 1, 0 // second page
    .fill 4096, 1, 0 // third page
    .global _mle_page_table_end
    _mle_page_table_end:


.section .text
    // Make room for MLE header at beginning
    .global _mle_hdr
    _mle_hdr:
    .fill TEMPORARY_MAX_MLE_HEADER_SIZE, 1, 0x90 ///XXX TODO just a guess; should really be sizeof(mle_hdr_t)

    .global _sl_start
    _sl_start:

#ifndef PERF_CRIT
    //Get cycle count using rdtsc; useful to evaluate how long DRTM
    //takes
    cpuid // Serializing instruction; causes more overhead :(
    rdtsc
    pushl %edx
    pushl %eax
#endif

    //save EAX, for AMD and the stub SENTER DRTM this contains the
    //64K aligned physical memory address where the sl was loaded
    //    movl %eax, %ebp
    // AMD leaves base addr in EAX, but Intel does not.  Since both CS and SS
    // are valid, read and align EIP to discover base addr

    // Figure out our own base address and place into EAX.
    // On AMD, this value is already in EAX.  However, on Intel
    // it is not guaranteed to be available (*might* be in ECX;
    // TODO is to check whether ECX value is reliable on Intel).
    // Cross-processor solution is call/pop/align.
    call 1f
1:  popl %eax // put EIP into EAX
    andl $0xffff0000, %eax // 64K-align
    movl %eax, %ebp

    // Other assumptions: common to both Intel and AMD:
    // EFLAGS_IF=0 (GIF=0 on AMD) so we are running with no interruptions
    // CR0.PG=0, i.e., paging is off

    // Determine processor type to perform some low-level initialization
    // after DRTM. On AMD CPUs, we need to clear R_INIT, DIS_A20M and
    // CR_DPD (to enable HDT access) in VM_CR_MSR.
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

    // If AMD CPU enable a few things that SKINIT disables.
    // Enable HDT debugging, also clear R_INIT and DIS_A20M.
    //XXX TODO Disable HDT debugging; represents a security vulnerability
sl_cpu_amd:
    movl $(VM_CR_MSR), %ecx
    rdmsr
    andl $(~(1<<VM_CR_DPD)), %eax
    andl $(~(1<<VM_CR_R_INIT)), %eax
    andl $(~(1<<VM_CR_DIS_A20M)), %eax
    wrmsr

    movl $(CPU_VENDOR_AMD), %edx
    jmp sl_cpu_common

sl_cpu_intel:
    movl $(CPU_VENDOR_INTEL), %edx
    jmp sl_cpu_common

    // Common code from now on
sl_cpu_common:
    // From here on we use EBP as our base and variable accesses will be as offsets
    // from _sl_header for position independence.

    // Cross-processor challenge:
    //   1. On AMD CS,SS are valid and DS is not.
    //   2. On Intel CS,DS are valid and SS is not.
    //   3. On both, CS is read-only.
    // Solution:
    //   1. Read memory using %cs segment-override prefix.
    //   2. Write memory using %ss and %ds on AMD and Intel, respectively.
    //      Processor vendor in register EDX from above CPU-specific code.


    // Setup GDT so that CS:base=sl base, limit=64K, type=code
    // DS,SS,ES: base=sl base, limit=64K, type=data
    // FS and GS: base=0, limit=4G, type=data (FLAT)

    //grab offset of sl_gdt_start
    movl $(sl_gdt_start), %ebx
    movl %ebp, %eax              //eax = sl base address
    movl %ebp, %ecx              //ecx = sl base address
    andl $0xFF000000, %eax       //eax = bits 24-31 of sl base address
    andl $0x00FF0000, %ecx       //ecx = bits 16-23 of sl base address
    shrl $16, %ecx               //bits 0-7 of ecx = bits 16-23 of sl base address
    orl %ecx, %eax               //bits 0-7 of eax = bits 16-23 of sl base address
                                 //bits 24-31 of eax = bits 24-31 of sl base address
                                 //eax is now in accordance with the high 32-bits
                                 //of a segment descriptor

    // EAX now contains a mask that can be ORed against GDT entries.
    // It contains [byte 3] [0] [0] [byte 2] of a segment descriptor's base address.

    // Get high 32-bits of 64-bit GDT entry for selector 0x08 (code)
    // and update it with the base address of the sl.
    movl %cs:12(%ebp, %ebx), %esi // 12 = 8-byte null descriptor + skip 4 low bytes
    andl  $0x00FFFF00, %esi       // Mask off any existing base addr bits that are set
    orl %eax, %esi                // OR in base addr bits computed in EAX
    // Put the updated entry back in the GDT (processor-specific)
    cmpl $(CPU_VENDOR_AMD), %edx
    jne 1f
    movl %esi, %ss:12(%ebp, %ebx) // AMD
    jmp 2f
    1: movl %esi, %ds:12(%ebp, %ebx) // Intel
    2:

    // Get high 32-bits of 64-bit GDT entry for selector 0x10 (data)
    // and update it with the base address of the sl.
    movl %cs:20(%ebp, %ebx), %esi
    andl $0x00FFFF00, %esi
    orl %eax, %esi
    // Put the updated entry back in the GDT (processor-specific)
    cmpl $(CPU_VENDOR_AMD), %edx
    jne 1f
    movl %esi, %ss:20(%ebp, %ebx) // AMD
    jmp 2f
    1: movl %esi, %ds:20(%ebp, %ebx) // Intel
    2:

    // Fixup linear address of GDT pseudo-descriptor using sl load-base.
    movl $(sl_gdt), %ebx
    cmpl $(CPU_VENDOR_AMD), %edx
    jne 1f
    addl %ebp, %ss:2(%ebp, %ebx) // AMD
    jmp 2f
    1: addl %ebp, %ds:2(%ebp, %ebx) // Intel
    2:

	//load GDT
    lgdt %cs:(%ebp,%ebx)

    movl $(sl_gdt), %ebx

    // Far jump to reload %cs
    jmpl $0x08, $(sl_startnew)

    // We start here with our new GDT CS selector
sl_startnew:
	// cpu vendor is in edx, move it into esi in case PERF_CRIT
	// is not definied, the following block will clobber edx
	movl	%edx, %esi

#ifndef PERF_CRIT
    // we are switching stacks so we need to save our performance
    // measurements in registers and then push them onto the new stack              
    popl %eax
    popl %edx              
#endif
              
    // Load new segment selectors for DS, SS and ES
    movw $0x10, %bx // XXX TODO Get rid of magic number
    movw %bx, %ds
    movw %bx, %es
    movw %bx, %ss

    // Load 4G flat selectors for FS and GS (used for TPM and TXT reg access)
    movw $0x18, %bx
    movw %bx, %fs
    movw %bx, %gs

    // Setup ESP to top of 64K (it will already be there on AMD)
    movl $0x10000, %esp // XXX TODO Get rid of magic number

/*#ifdef __INIT_LATE__
    //setup 115200,8n1 on ttyS0 
    call raw_serial_init
    mov $0x3fd, %edx // control register for com1
1:  in (%dx), %al    // read status into AL
    test $0x20, %al  // check for ready
    je 1b            // keep trying
    mov $0x3f8, %edx // data register for com1
    mov $0x40, %al   // output an @ character
    out %al, (%dx)
#endif*/


#ifndef PERF_CRIT
    // push measurements onto the new stack
    pushl %edx
    pushl %eax              
#else
    pushl $0x00000000
    pushl $0x00000000
#endif
              
    pushl %ebp			//SL base address
    pushl %esi			//cpu vendor
    call emhf_sl_main	//call SL main routine

    // We should never get here
    spinforever:
        jmp spinforever
    hlt

//----------------------------------------------------------------------
// DATA
//----------------------------------------------------------------------

.section .data

    //the secure loader GDT
    sl_gdt:
    .word    sl_gdt_end - sl_gdt_start + 1     // XXX WAS PREVIOUSLY -1 !!!
    .long    sl_gdt_start                      // This will be fixed up to sl load-base
    .align    16
    sl_gdt_start:
    .quad    0x0000000000000000                //0x00: NULL selector
    .quad    0x00cf9a000000ffff                //0x08: 4G CODE selector with sl load-base
    .quad    0x00cf92000000ffff                //0x10: 4G DATA selector with sl load-base
    .quad   0x00cf92000000ffff                 //0x18: 4G DATA selector with zero base
    .quad    0x0000000000000000                //0x20: NULL selector
    sl_gdt_end:


//----------------------------------------------------------------------
// STACK
//----------------------------------------------------------------------

// sl stack, this is just a placeholder and ensures that the linker
// actually "allocates" the stack up until 0x10000
.section .sl_stack
    .fill 2048, 1, 0
