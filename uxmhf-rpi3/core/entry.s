/*
	entry stub

	author: amit vasudevan (amitvasudevan@acm.org)
*/

.section ".text"

.globl entry
entry:

	/* turn on unaligned memory access */
	mrc p15, #0, r4, c1, c0, #0
	orr r4, #0x400000				/*set U bit (bit-22) */
	mcr p15, #0, r4, c1, c0, #0

	/* load stack and start C land */
	ldr sp, =stack_top
	bl main

halt:
	b halt


.globl entry_svc
entry_svc:

	/* load stack and start C land */
	ldr sp, =stacksvc_top
	bl main_svc

hlt_entry_svc:
	b hlt_entry_svc


.globl chainload_os
chainload_os:
//	ldr r3, =0x30800000
	ldr r3, =0x00008000
	blx r3


.global cpumodeswitch_hyp2svc
cpumodeswitch_hyp2svc:
	msr ELR_hyp, r0			//store address to begin execution in SVC mode in ELR_hyp
    mrs r0, cpsr_all
    and r0, r0, #0xffffffe0
    orr r0, r0, #0x13
    msr SPSR_hyp, r0
	eret					//this will start executing at the address provided in SVC mode


.section ".stack", "aw"
	.balign 8
	.global stack
	stack:	.space	256
	.global stack_top
	stack_top:

	.balign 8
	.global stacksvc
	stacksvc:	.space	256
	.global stacksvc_top
	stacksvc_top:



