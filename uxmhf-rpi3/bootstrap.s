/*
	bootstrap code

	resides in a page below the actual os kernel
	transfers control to the initramfs image (which is the
	microhypervisor image)

	author: amit vasudevan (amitvasudevan@acm.org)
*/

.globl bootstrap_entry
bootstrap_entry:
	ldr r3, =0x30000000
	blx r3

halt:
	b halt
