/*
	SVC mode verctor table and stubs

	author: amit vasudevan (amitvasudevan@acm.org)
*/


.section ".text"
/*
	G1.12.1 (Table G1-6 ARMv8)
	SVC vector table format:
	offsets:
		0x0: 	not used
		0x4: 	undefined instruction
		0x8: 	SVC (supervisor call)
		0x0C:	prefetch abort
		0x10: 	data abort
		0x14:	not used
		0x18:	IRQ
		0x1C:	FIQ
*/

/* need lower 5 bits (0-4) of the table address as 0, so use balign 32 */
	.balign	32
	.global g_svcvtable
g_svcvtable:
	b svcvtable_reserved_handler
	b svcvtable_reserved_handler
	b svcvtable_svc_handler
	b svcvtable_reserved_handler
	b svcvtable_reserved_handler
	b svcvtable_reserved_handler
	b svcvtable_reserved_handler
	b svcvtable_reserved_handler

	.balign 32
	.global	svcvtable_reserved_handler
svcvtable_reserved_handler:
	srh_halt:
	b srh_halt


/*
	G1.12.3 ARMv8
	exception return address is stored in the LR for the mode to which
	the exception is taken, in this case LR_svc and
	points to the instruction *after* the SVC instruction (Table G1-9)
*/
	.global	svcvtable_svc_handler
svcvtable_svc_handler:
	ldr sp, =svcvtable_stack_top

	/*
		save LR_svc
	*/
	push {lr}

	/* 5.1.1 AAPCS
	   callee preserves r4-r8, r10, r11, r13 (SP)
	   save the rest
	*/
	push {r0}
	push {r1}
	push {r2}
	push {r3}
	push {r9}
	push {r12}

	/* invoke C handler */
	bl svc_handler


	/* restore all saved registers */
	pop	{r12}
	pop	{r9}
	pop	{r3}
	pop	{r2}
	pop	{r1}
	pop	{r0}


	pop {lr}

	/*
		G1.13.1 ARMv8
		exception returns from SVC mode is made via ERET instruction
		which basically returns to LR_svc and restores appropriate
		PE (processor execution) state
	*/
	eret





.section ".stack"
	.balign 8
	.global svcvtable_stack
	stack:	.space	256
	.global svcvtable_stack_top
	svcvtable_stack_top:


