/*
	HYP mode verctor table and stubs

	author: amit vasudevan (amitvasudevan@acm.org)
*/


.section ".text"
/*
	G1.12.1 (Table G1-6 ARMv8)
	HYP vector table format:
	offsets:
		0x0: 	not used
		0x4: 	undefined instruction form HYP mode
		0x8: 	HVC in HYP mode
		0x0C:	prefetch abort from HYP mode
		0x10: 	data abort from HYP mode
		0x14:	HVC in non-HYP mode
		0x18:	IRQ
		0x1C:	FIQ
*/

/* need lower 5 bits (0-4) of the table address as 0, so use balign 32 */
	.balign	32
	.global g_hypvtable
g_hypvtable:
	b hypvtable_reserved_handler
	b hypvtable_reserved_handler
	b hypvtable_hyphvc_handler
	b hypvtable_reserved_handler
	b hypvtable_reserved_handler
	b hypvtable_hypsvc_handler
	b hypvtable_reserved_handler
	b hypvtable_reserved_handler

	.balign 32
	.global	hypvtable_reserved_handler
hypvtable_reserved_handler:
	ldr sp, =hypvtable_rsvhandler_stack_top
	bl hyp_rsvhandler

	hrh_halt:
	b hrh_halt


/*
	G1.12.3 ARMv8
	exception return address is stored in ELR_hyp register and
	points to the instruction *after* the HVC instruction (Table G1-9)
*/
	.global	hypvtable_hyphvc_handler
hypvtable_hyphvc_handler:
	//ldr sp, =hypvtable_stack_top

	/* G1.9.2 (Figure G1-3)
	   HYP mode uses LR_usr, i.e, does not have LR banking, so save
	   since we are going to be using LR for C calling
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
	bl hyphvc_handler


	/* restore all saved registers */
	pop	{r12}
	pop	{r9}
	pop	{r3}
	pop	{r2}
	pop	{r1}
	pop	{r0}

	pop	{lr}

	/*
		G1.13.1 ARMv8
		exception returns from HYP mode is made via ERET instruction
		which basically returns to ELR_hyp and restores appropriate
		PE (processor execution) state
	*/
	eret



/*
	G1.12.3 ARMv8
	exception return address is stored in ELR_hyp register and
	points to the instruction *after* the HVC instruction (Table G1-9)
*/
	.global	hypvtable_hypsvc_handler
hypvtable_hypsvc_handler:
	ldr sp, =hypvtable_hypsvc_stack_top

	/* G1.9.2 (Figure G1-3)
	   HYP mode uses LR_usr, i.e, does not have LR banking, so save
	   since we are going to be using LR for C calling
	*/
	push {lr}


	/* 5.1.1 AAPCS
	   callee preserves r4-r8, r10, r11, r13 (SP)
	   save the rest
	*/
	//push {r14}
	//push {r13}
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


	/* invoke C handler */
	mov r0, sp
	bl hypsvc_handler


	/* restore all saved registers */
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
	//pop {r13}
	//pop {r14}

	pop	{lr}

	/*
		G1.13.1 ARMv8
		exception returns from HYP mode is made via ERET instruction
		which basically returns to ELR_hyp and restores appropriate
		PE (processor execution) state
	*/
	eret



.section ".stack"
	.balign 8
	.global hypvtable_stack
	stack:	.space	8192
	.global hypvtable_stack_top
	hypvtable_stack_top:

	.balign 8
	.global hypvtable_hypsvc_stack
	hypvtable_hypsvc_stack:	.space	16384
	.global hypvtable_hypsvc_stack_top
	hypvtable_hypsvc_stack_top:

	.balign 8
	.global hypvtable_rsvhandler_stack
	hypvtable_rsvhandler_stack:	.space	8192
	.global hypvtable_rsvhandler_stack_top
	hypvtable_rsvhandler_stack_top:


