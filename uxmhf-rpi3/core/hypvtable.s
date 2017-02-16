/*
	HYP mode verctor table and stubs

	author: amit vasudevan (amitvasudevan@acm.org)
*/


	.section .text
/*
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

	.balign	32
	.global g_hypvtable
g_hypvtable:
	b hypvtable_reserved_handler
	b hypvtable_reserved_handler
	b hypvtable_reserved_handler
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



.section ".stack"
	.balign 8
	.global hypvtable_stack
	stack:	.space	256
	.global hypvtable_stack_top
	hypvtable_stack_top:


