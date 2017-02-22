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


.globl entry_svc
entry_svc:

	/* load stack and start C land */
	ldr sp, =stacksvc_top
	bl main_svc

hlt_entry_svc:
	b hlt_entry_svc



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


.globl sysreg_read_spsr_hyp
sysreg_read_spsr_hyp:
	mrs r0, SPSR_hyp
	bx lr


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


.global sysreg_read_hcr
sysreg_read_hcr:
	mrc p15, 4, r0, c1, c1, 0
	bx lr

.global sysreg_write_hcr
sysreg_write_hcr:
	mcr p15, 4, r0, c1, c1, 0
	bx lr


.global hypcall
hypcall:
	hvc #0
	bx lr


.global cpumodeswitch_hyp2svc
cpumodeswitch_hyp2svc:
	msr ELR_hyp, r0			//store address to begin execution in SVC mode in ELR_hyp
    mrs r0, cpsr_all
    and r0, r0, #0xffffffe0
    orr r0, r0, #0x13
    msr SPSR_hyp, r0
	eret					//this will start executing at the address provided in SVC mode


.section ".stack"
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

