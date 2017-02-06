/*
	entry stub

	author: amit vasudevan (amitvasudevan@acm.org)
*/

.globl entry
entry:
	mov sp, #0x9000
	bl main

halt:
	b halt


.globl peek32
peek32:
    str r1,[r0]
    bx lr

.globl poke32
poke32:
    ldr r0,[r0]
    bx lr

