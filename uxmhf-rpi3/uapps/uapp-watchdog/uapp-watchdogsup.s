/*
	uapp watchdog low-level support routines

	author: amit vasudevan (amitvasudevan@acm.org)
*/


.section ".text"


	.balign 32
	.global	hypvtable_fiq_handler0
hypvtable_fiq_handler0:
	ldr sp, =hypvtable_fiqhandler_stack_top0

	push {lr}

	push {r12}
	push {r11}
	push {r10}
	push {r9}
	push {r8}
	push {r7}
	push {r6}
	push {r5}
	push {r4}
	push {r3}
	push {r2}
	push {r1}
	push {r0}

	bl hyp_fiqhandler

	// restore all saved registers
	pop {r0}
	pop {r1}
	pop {r2}
	pop {r3}
	pop {r4}
	pop {r5}
	pop {r6}
	pop {r7}
	pop {r8}
	pop {r9}
	pop {r10}
	pop {r11}
	pop {r12}

	pop	{lr}

	eret




.section ".stack"

	.balign 8
	.global hypvtable_fiqhandler_stack0
	hypvtable_fiqhandler_stack0:	.space	8192
	.global hypvtable_fiqhandler_stack_top0
	hypvtable_fiqhandler_stack_top0:


