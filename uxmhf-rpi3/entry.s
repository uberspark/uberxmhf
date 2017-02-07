/*
	entry stub

	author: amit vasudevan (amitvasudevan@acm.org)
*/

.globl entry
entry:
	/*mov sp, #0x9000
	bl main*/
	mov r3, #0x8000
	blx r3

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

