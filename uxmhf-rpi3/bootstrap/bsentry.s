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


.section ".data"

	.align 2
	.global g_oskrnl_startaddr
	.type g_oskrnl_startaddr, %object
	.size g_oskrnl_startaddr, 4
	g_oskrnl_startaddr:	.word	0x8000

	.align 2
	.global g_oskrnl_size
	.type g_oskrnl_size, %object
	.size g_oskrnl_size, 4
	g_oskrnl_size:	.word	0x420000

	.align 2
	.global g_core_startaddr
	.type g_core_startaddr, %object
	.size g_core_startaddr, 4
	g_core_startaddr:	.word	0x428000


	.align 2
	.global g_core_size
	.type g_core_size, %object
	.size g_core_size, 4
	g_core_size:	.word	0x1000


