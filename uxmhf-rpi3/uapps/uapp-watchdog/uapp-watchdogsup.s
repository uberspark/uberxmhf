/*
	uapp watchdog low-level support routines

	author: amit vasudevan (amitvasudevan@acm.org)
*/


.section ".text"


	.balign 32
	.global	uapp_watchdog_fiq_handler
uapp_watchdog_fiq_handler:
	ldr sp, =uapp_watchdog_fiqhandler_stack_top

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

	bl uapp_watchdog_fiqhandler

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
	.global uapp_watchdog_fiqhandler_stack
	uapp_watchdog_fiqhandler_stack:	.space	8192
	.global uapp_watchdog_fiqhandler_stack_top
	uapp_watchdog_fiqhandler_stack_top:


