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





.globl call_core
call_core:
	ldr r3, =0x30000000
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
	//g_oskrnl_size:	.word	0x41E000
	g_oskrnl_size:	.word	0x41F000
	//g_oskrnl_size:	.word	0x3ed000

	.align 2
	.global g_core_startaddr
	.type g_core_startaddr, %object
	.size g_core_startaddr, 4
	//g_core_startaddr:	.word	(0x41E000+0x8000)
	g_core_startaddr:	.word	(0x41F000+0x8000)
	//g_core_startaddr:	.word	(0x3ed000+0x8000)


	.align 2
	.global g_core_size
	.type g_core_size, %object
	.size g_core_size, 4
	g_core_size:	.word	0xA00000


	.align 2
	.global g_guestos_startaddr
	.type g_guestos_startaddr, %object
	.size g_guestos_startaddr, 4
	//	g_guestos_startaddr:	.word	(0x41E000+0x8000+0x800000)
	g_guestos_startaddr:	.word	(0x41F000+0x8000+0xA00000)
	//g_guestos_startaddr:	.word	(0x3ed000+0x8000+0x800000)


	.align 2
	.global g_guestos_size
	.type g_guestos_size, %object
	.size g_guestos_size, 4
	g_guestos_size:	.word	0x3000

