/*
	entry stub

	author: amit vasudevan (amitvasudevan@acm.org)
*/

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


.globl mmio_write32
mmio_write32:
    str r1,[r0]
    bx lr

.globl mmio_read32
mmio_read32:
    ldr r0,[r0]
    bx lr


.globl chainload_os
chainload_os:
	ldr r3, =0x00008000
	blx r3



.globl sysreg_read_scr
sysreg_read_scr:
	mrc p15, 0, r0, c1, c1, 0
	bx lr

.globl sysreg_read_cpsr
sysreg_read_cpsr:
	mrs r0, cpsr
	bx lr

.global sysreg_read_hvbar
sysreg_read_hvbar:
	mrc p15, 4, r0, c12, c0, 0
	bx lr


.global sysreg_write_hvbar
sysreg_write_hvbar:
	mcr p15, 4, r0, c12, c0, 0
	bx lr


.global hypcall
hypcall:
	hvc #0
	bx lr


.global cpumodeswitch_hyp2svc
cpumodeswitch_hyp2svc:
	msr ELR_hyp, r0			//store address to begin execution in SVC mode in ELR_hyp
	msr	spsr_cxsf, #0x13	//change spsr mode to SVC(ARM_MODE_SVC) //you cannot switch to HYP mode directly from secure world, doh!
	eret					//this will start executing at the address provided in SVC mode

.section ".stack"
	.balign 8
	.global stack
	stack:	.space	256
	.global stack_top
	stack_top:
