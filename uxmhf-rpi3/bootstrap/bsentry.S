/*
	bootstrap code

	resides in a page below the actual os kernel
	transfers control to the initramfs image (which is the
	microhypervisor image)

	author: amit vasudevan (amitvasudevan@acm.org)
*/
#include <config.h>

.globl bootstrap_entry
bootstrap_entry:
	ldr sp, =0x00007f00
	bl bsmain

halt:
	b halt


.globl call_core
call_core:
	ldr r3, =(UXMHF_CORE_START_ADDR)
	blx r3

