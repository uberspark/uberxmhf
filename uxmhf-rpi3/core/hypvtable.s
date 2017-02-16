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
	b hypvtable_reserved_handler
	b hypvtable_reserved_handler
	b hypvtable_reserved_handler

	.balign 32
	.global	hypvtable_reserved_handler
hypvtable_reserved_handler:
	hrh_halt:
	b hrh_halt


/*
	G1.12.3 ARMv8
	exception return address is stored in ELR_hyp register
*/
	.global	hypvtable_hyphvc_handler
hypvtable_hyphvc_handler:
	ldr sp, =hypvtable_stack_top
	bl hyphvc_handler

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
	stack:	.space	256
	.global hypvtable_stack_top
	hypvtable_stack_top:


