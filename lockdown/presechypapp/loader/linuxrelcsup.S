#include <target.h>

	.section .text

	.global boot_linux
boot_linux:
	
	/* Disable interrupt */
	//cli

/* This jump switches to the handler that force the CPU
 * into 16-bit protected mode */
	movl	$(LOADER_REAL_START + linux_boot - realmode_start), %eax
	jmp	*%eax

/* We should never return. Force CPU to panic in case we do. */
	ud2	/* Undefined opcode */

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

	