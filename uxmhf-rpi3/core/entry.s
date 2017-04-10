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


.globl entry_svc
entry_svc:
	hvc #0
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



.section ".stack", "aw"

	.balign 8
	.global stacksvc
	stacksvc:	.space	8192
	.global stacksvc_top
	stacksvc_top:


	.balign 8
	.global cpu_stacks
	cpu_stacks:	.space	(8192 * 4)



