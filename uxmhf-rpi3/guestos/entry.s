/*
	entry stub

	author: amit vasudevan (amitvasudevan@acm.org)
*/

.globl entry
entry:

	/* load stack and start C land */
	ldr sp, =stack_top
	bl main

halt:
	b halt




.globl mmio_write32
mmio_write32:
    str r1,[r0]
    bx lr

.globl mmio_read32
mmio_read32:
    ldr r0,[r0]
    bx lr




.global hypcall
hypcall:
	hvc #0
	bx lr


.globl sysreg_read_cpsr
sysreg_read_cpsr:
	mrs r0, cpsr
	bx lr


.section ".stack"

	.balign 8
	.global stack
	stack:	.space	256
	.global stack_top
	stack_top:

