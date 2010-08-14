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

/* boot.S - TrustVisor loader code. This code is loaded by grub at 
 * physical address 24MB.  It obtains the e820 map from grub, cleans
 * the map, and figures out the max page frame number. It passes this
 * value to TrustVisor by writing it to the top of TrustVisor's
 * initialization code stack. It relocates TrustVisor to 0x1e00000 (30 MB),
 * the kernel to 1 MB, and initrd to 64M. Finally, it transfers control
 * to the Linux kernel's bootstrap code, after switching the CPU into
 * real mode. Linux's bootstrap code calls TrustVisor using skinit. Linux's
 * bootstrap code also passes to TrustVisor the start and end addresses of
 * the kernel's main code segment, init code segment, alt instructions
 * segment, the size of the uncompressed kernel image, a pointer to
 * the kernel's gdt (set up by the kernel's bootstrap code), and a
 * pointer to the kernel's boot parameters by pushing these values on
 * TrustVisor's initialization stack.
 XXX I'M PRETTY SURE THIS IS STALE; THE LINUX KERNEL IS NO LONGER
   INVOLVED IN INVOKING SKINIT; IT IS CALLED IN THIS FILE. -Jon
   2009.10.29
 */
/* Written by Ning Qu and Arvind Seshadri */

#include <types.h>	
#include <multiboot.h>
#include <loader.h>
#include <msr.h>
#include <visor.h>
			
	.section "loader_text"
/* start of code segment */
ENTRY(loader)
	jmp	__loader
	
/* Multiboot header for ELF binaries. See Multiboot Specification 
 * for details 
 */     
	.align 4
	.long MULTIBOOT_HEADER_MAGIC
	.long MULTIBOOT_HEADER_FLAGS
	.long -(MULTIBOOT_HEADER_MAGIC + MULTIBOOT_HEADER_FLAGS)
	
__loader:	
/* Protection already enabled when we are called by the bootloader.
 * Only %cs is guaranteed to be correct 
 * eax has bootloader signature and ebx has pointer to multiboot struct 
 */
	lgdt	%cs:loader_gdt_descr
	movw	$(__LOADER_DS), %cx
/* Load the data segment selector */
	movw	%cx, %ds	
	movw	%cx, %es
	movw	%cx, %fs
	movw	%cx, %gs
/* Long jump to load cs */	
	ljmp	$(__LOADER_CS), $(1f)
/* Set up a stack. lss loads the far pointer at memory location visor_stack
 * into ss and esp. Far pointers are pointers in the seg:offset format
 */
1:	lss	loader_stack, %esp
/* Relocate esp to top of stack */	
	addl	$(LOADER_STACK_SIZE), %esp

/* Clear eflags */
	pushl	$0
	popf

/* Check if we were loaded by a multiboot compliant loader */
	cmpl	$(MULTIBOOT_BOOTLOADER_MAGIC), %eax
	jnz	not_multiboot

/* Save the Multiboot info structure for later use. */
	push    %ebx
        
/* Relocate Linux and TrustVisor */
	mov	%ebx, %eax
	call	relocate

/* Enable SVME support */
	movl 	$MSR_VM_CR, %ecx
        rdmsr
	andl	$(~(0x00000011)), %eax
	wrmsr

/* Prepare for skinit */
	call	prepare_skinit

/* Disable interrupt */
	cli

        movl $VISOR_LOAD_START, %eax
        skinit

/* This jump switches to the handler that force the CPU
 * into 16-bit protected mode */
	movl	$(LOADER_REAL_START + linux_boot - realmode_start), %eax
	jmp	*%eax

/* We should never return. Force CPU to panic in case we do. */
	ud2	/* Undefined opcode */
	
/* prints a null-termintated string to video buffer at 0xb8000 */
/* Input parameters:	 %esi is pointer to string */
print_string_boot:
	cld			
	movl	$0xb8000, %edi	
1:	movb	(%esi), %cl
	test	%cl, %cl		/* test if null character */
	je	2f
/* write %cl to video buffer. increment esi and edi */
	movsb
	movb	$7, %cl		/* attribute byte into %cl */
/* write attribute byte to video buffer. increment edi */
	stosb
	jmp	1b
2:	ret

                
not_multiboot_compliant_msg:
	.asciz "Not a Multiboot Compliant bootloader"
not_multiboot:
	pushl	%esi
	pushl	%ecx
	movl	$not_multiboot_compliant_msg, %esi
	movl	$print_string_boot, %ecx
	call	*%ecx
	popl	%ecx
	popl	%esi
1:	jmp	1b			/* inifinte loop */



/*
 * Trampoline code for the APs.
 * All this is realmode code that should fit within a 64K segment
 * and upon entry only %cs is valid.
 */
ENTRY(svm_ap_trampoline)
        .code16
        /* %cs is the only thing valid at this point */
        mov     %cs, %ax
        mov     %ax, %ds

        /* enable SVM so we can do an stgi */
        movl    $MSR_EFER, %ecx
        rdmsr
        orb     $0x10, %ah
        wrmsr

        /* clear A20|INIT|DPD bits */
        movl    $MSR_K8_VM_CR, %ecx
        rdmsr
        andb    $~7, %al
        wrmsr

        /* STGI is a protected mode instruction */
        mov     $1, %ax
        lmsw    %ax
        cli
        stgi

        /* enter our 32-bit world */
        lidtl   svm_ap_idt_descr - svm_ap_trampoline
        lgdtl   svm_ap_gdt_descr - svm_ap_trampoline
        ljmpl   $(__LOADER_CS), $svm_ap_init
        .code32

        .align  16
svm_ap_gdt_descr:
        .word   loader_gdt_end - loader_gdt - 1
        .long   loader_gdt

        .align  16
svm_ap_idt_descr:
        .word   0
        .long   0

ENTRY(svm_ap_trampoline_size)
        .long   . - svm_ap_trampoline

/*
 * Initialization code for the APs
 */
        .text
ENTRY(svm_ap_init)
        /* setup the rest of the 32-bit world */
        lgdt    %cs:loader_gdt_descr
        mov     $0x10, %ecx
        mov     %ecx, %ds
        mov     %ecx, %es
        mov     %ecx, %fs
        mov     %ecx, %gs
        mov     %ecx, %ss
        ljmp    $(__LOADER_CS), $(1f)
1:      lidt    svm_ap_idt_descr

        /* get initial APIC ID for this processor */
        mov     $0x01, %eax
        xor     %ebx, %ebx
        cpuid
        shr     $24, %ebx
        and     $0xff, %ebx

        /* set stack as id-based offset from AP stack base */
        mov     $STARTUP_STACK_SIZE, %eax
        mul     %ebx
        sub     $STARTUP_STACK_SIZE, %eax
        mov     $ap_stacks, %ecx
        sub     %eax, %ecx
        mov     %ecx, %esp

        push    %ebx
        call    svm_ap_wakeup

        
        
/*
 * This is the Global Descriptor Table
 *
 *  An entry, a "Segment Descriptor", looks like this:
 *
 * 31          24         19   16                 7           0
 * ------------------------------------------------------------
 * |             | |B| |A|       | |   |1|0|E|W|A|            |
 * | BASE 31..24 |G|/|0|V| LIMIT |P|DPL|  TYPE   | BASE 23:16 |
 * |             | |D| |L| 19..16| |   |1|1|C|R|A|            |
 * ------------------------------------------------------------
 * |                             |                            |
 * |        BASE 15..0           |       LIMIT 15..0          |
 * |                             |                            |
 * ------------------------------------------------------------
 *
 *  Note the ordering of the data items is reversed from the above
 *  description.
 */

        .p2align        2       /* force 4-byte alignment */
ENTRY(realmode_start)
ENTRY(linux_gdt)
        .word   0, 0
        .byte   0, 0, 0, 0

        /* code segment */
        .word   0xFFFF, 0
        .byte   0, 0x9A, 0xCF, 0

        /* data segment */
        .word   0xFFFF, 0
        .byte   0, 0x92, 0xCF, 0

        /* 16 bit real mode CS */
        .word   0xFFFF, 0
        .byte   0x2, 0x9E, 0, 0

        /* 16 bit real mode DS */
        .word   0xFFFF, 0
        .byte   0, 0x92, 0, 0


/* this is the GDT descriptor */
linux_gdtdesc:
        .word   0x27                    /* limit */
        .long   LOADER_REAL_START	/* addr */

ENTRY(linux_boot)

        /* just in case, set GDT */
        lgdt    linux_gdtdesc - linux_gdt + LOADER_REAL_START

        /* set up segment limits */
        movw    $__ENTRY_DS, %ax
        movw    %ax, %ds
        movw    %ax, %es
        movw    %ax, %fs
        movw    %ax, %gs
        movw    %ax, %ss

        /* this might be an extra step */
        ljmp    $__ENTRY_CS, $(tmpcseg - linux_gdt)     /* jump to a 16 bit segment */

tmpcseg:
        .code16

        /* clear the PE bit of CR0 */
        movl    $0x10, %eax
        movl    %eax, %cr0

        /* flush prefetch queue, reload %cs */
        data32 ljmp    $(LOADER_REAL_START >> 4), $(realcseg - linux_gdt)

realcseg:
        /* we are in real mode now
         * set up the real mode segment registers : DS, SS, ES
         */
        /* zero %eax */
        xorl    %eax, %eax

        movw    %ax, %ds
        movw    %ax, %es
        movw    %ax, %fs
        movw    %ax, %gs
        movw    %ax, %ss

        movw    $LINUX_BOOT_DS, %ax
        movw    %ax, %ss
        movw    $LINUX_BOOT_SP, %sp

        movw    %ax, %ds
        movw    %ax, %es
        movw    %ax, %fs
        movw    %ax, %gs

        data32 ljmp	$LINUX_BOOT_CS, $0
ENTRY(realmode_end)
        .code32

/* Create a separate section for all initialized data */
	.section "loader_static_data", "w"
/* GDT descriptor for the loader */	
	.word	0			/* 32-bit align gdt descr */
loader_gdt_descr:	
	.word	loader_gdt_end - loader_gdt - 1	/* gdt limit */
	.long	loader_gdt		/* gdt base */

/* GDT for loader */
ENTRY(loader_gdt)
	.quad	0x0000000000000000	/* NULL descriptor */
	.quad	0x00cf9a000000ffff	/* 4GB 32-bit code seg descr */
	.quad	0x00cf92000000ffff	/* 4GB 32-bit data seg descr */
/* descriptors for starting up APS */
tss_descr:  /* tss (may be unnecessary), not sure yet */
        .word   0xffff          /* limit = 4GB */
        .word   0x0000          /* base = 0 */
        .word   0x8900          /* system segment, 32b available TSS */
        .word   0x008f          /* granularity = 4096 */
cs16_desc:  /* cs16 */
        .word   0xffff          /* limit = 4GB */
        .word   0x0000          /* base = 0 */
        .word   0x9b00          /* read + exec + accessed */
        .word   0x008f          /* granularity = 4096, D = 0 */
ds16_desc:  /* ds16 */
        .word   0xffff          /* limit = 4GB */
        .word   0x0000          /* base = 0 */
        .word   0x9300          /* read + exec + accessed */
        .word   0x008f          /* granularity = 4096, D = 0 */
                /* end (unused) */
        .quad   0x0000000000000000
loader_gdt_end:

	ALIGN	
/* Stack segment descriptor */
ENTRY(loader_stack)
	.long	stack 
	.long	__LOADER_DS

	.section "loader_stack_seg", "w"
ENTRY(stack)
	.fill	LOADER_STACK_SIZE, 1, 0


/* Startup stacks for APs, NR_CPUS-1 because BSP not included */
ap_stacks_end:
        .fill STARTUP_STACK_SIZE * (NR_CPUS-1), 1, 0
ap_stacks:

