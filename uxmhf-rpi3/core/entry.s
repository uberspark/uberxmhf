/*
	entry stub

	author: amit vasudevan (amitvasudevan@acm.org)
*/

.section ".text"

//r0, r1 and r2 are set by the boot-loader and need to
//be preserved
.globl entry
entry:

 	mrc p15, #0, r3, c0, c0, #5 	//read MPIDR
 	and r3, #3						//mask off the CPUID value
	add r4, r3, #1					//r4 = index into cpu_stacks

	ldr sp, =cpu_stacks				//load cpu_stacks base into stack-pointer
	mov r5, #8192
	mul r6, r4, r5					//r6 is the offset to add based on index (r4)
	add sp, sp, r6					//sp is the top-of-stack for this cpu

	bl main

halt:
	b halt




//r0,r1,r2 go through to the guest os
//r3 contains the starting address to execute the guestos
//clobbers r7,r9
.globl chainload_os
chainload_os:

	mov	r7, #0
	//mcr	p15, 4, r7, c1, c1, 0	// HCR=0
	mcr	p15, 4, r7, c1, c1, 2	// HCPTR=0
	mcr	p15, 4, r7, c1, c1, 3	// HSTR=0

	//mcr	p15, 4, r7, c1, c0, 0	// HSCTLR=0

	mrc	p15, 4, r7, c1, c1, 1	// HDCR
	and	r7, #0x1f				// Preserve HPMN
	mcr	p15, 4, r7, c1, c1, 1	// HDCR


	// make CNTP_* and CNTPCT accessible from guest
	mrc	p15, 0, r7, c0, c1, 1	// ID_PFR1
	lsr	r7, #16
	and	r7, #0xf
	cmp	r7, #1
	bne	1f
	mrc	p15, 4, r7, c14, c1, 0	// CNTHCTL
	orr	r7, r7, #3				// PL1PCEN | PL1PCTEN
	mcr	p15, 4, r7, c14, c1, 0	// CNTHCTL
	mov	r7, #0
	mcrr	p15, 4, r7, r7, c14	// CNTVOFF

	//disable virtual timer
	mrc	p15, 0, r7, c14, c3, 1	// CNTV_CTL
	bic	r7, #1					// Clear ENABLE
	mcr	p15, 0, r7, c14, c3, 1	// CNTV_CTL

1:

	mrs	r9 , cpsr
	eor	r9, r9, #0x0000001a		//HYP_MODE
	tst	r9, #0x0000001f			//MODE_MASK
	bic	r9 , r9 , #0x0000001f	//MODE_MASK
	orr	r9 , r9 , #(0x00000080 | 0x00000040 | 0x00000013) //PSR_I_BIT | PSR_F_BIT | SVC_MODE
	orr	r9, r9, #0x00000100		//PSR_A_BIT
	msr	spsr_cxsf, r9
	msr ELR_hyp, r3			//store address to begin execution in SVC mode in ELR_hyp
	eret


.globl chainload_os_svc
chainload_os_svc:
	blx r0


.global cpumodeswitch_hyp2svc
cpumodeswitch_hyp2svc:
	msr ELR_hyp, r3			//store address to begin execution in SVC mode in ELR_hyp
    mrs r5, cpsr_all
    and r5, r5, #0xffffffe0
    orr r5, r5, #0x13
    msr SPSR_hyp, r5
	eret					//this will start executing at the address provided in SVC mode



.globl secondary_cpu_entry
secondary_cpu_entry:

 	mrc p15, #0, r0, c0, c0, #5 	//read MPIDR
 	and r0, #3						//mask off the CPUID value
	add r1, r0, #1					//r1 = index into cpu_stacks

	ldr sp, =cpu_stacks				//load cpu_stacks base into stack-pointer
	mov r2, #8192
	mul r3, r2, r1					//r3 is the offset to add based on index (r1)
	add sp, sp, r3					//sp is the top-of-stack for this cpu

	bl secondary_main				//r0 is the cpuid

secondary_cpu_entry_halt:
	b secondary_cpu_entry_halt



.globl secondary_cpu_entry_svc
secondary_cpu_entry_svc:

 	mrc p15, #0, r0, c0, c0, #5 	//read MPIDR
 	and r0, #3						//mask off the CPUID value
	add r1, r0, #1					//r1 = index into cpu_stacks

	ldr sp, =cpu_stacks_svc				//load cpu_stacks base into stack-pointer
	mov r2, #8192
	mul r3, r2, r1					//r3 is the offset to add based on index (r1)
	add sp, sp, r3					//sp is the top-of-stack for this cpu

	bl secondary_main_svc				//r0 is the cpuid

secondary_cpu_entry_svc_halt:
	b secondary_cpu_entry_svc_halt





.section ".stack", "aw"

	.balign 8
	.global cpu_stacks
	cpu_stacks:	.space	(8192 * 4)

	.balign 8
	.global cpu_stacks_svc
	cpu_stacks_svc:	.space	(8192 * 4)


