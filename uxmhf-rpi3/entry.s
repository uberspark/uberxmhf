/*
	entry stub

	author: amit vasudevan (amitvasudevan@acm.org)
*/

.globl entry
entry:
	ldr sp, =0x00007c00
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


.globl chainload_os
chainload_os:
	ldr r3, =0x00008000
	blx r3
