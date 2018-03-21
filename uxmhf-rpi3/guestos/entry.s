/*
	entry stub

	author: amit vasudevan (amitvasudevan@acm.org)
*/

.globl entry
entry:

	/* load stack and start C land */
	ldr sp, =stack_top
	bl main

halt:
	b halt


.global cpumodeswitch_svc2usr
cpumodeswitch_svc2usr:
	cps	#0x10
	ldr sp, =usrstack_top
	blx	r0


.section ".stack", "aw"

	.balign 8
	.global stack
	stack:	.space	256
	.global stack_top
	stack_top:

	.balign 8
	.global usrstack
	usrstack:	.space	256
	.global usrstack_top
	usrstack_top:
