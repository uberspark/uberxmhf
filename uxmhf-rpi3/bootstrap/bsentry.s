/*
	bootstrap code

	resides in a page below the actual os kernel
	transfers control to the initramfs image (which is the
	microhypervisor image)

	author: amit vasudevan (amitvasudevan@acm.org)
*/

.globl bootstrap_entry
bootstrap_entry:
	ldr sp, =0x00007f00
	bl bsmain

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
