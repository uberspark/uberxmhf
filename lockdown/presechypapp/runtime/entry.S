#include <target.h>



//------------------------------------------------------------------------------
.altmacro
.macro runtime_emitidtstub vector
	.section .text
	runtime_idtstub&vector&:
		pusha
		movw	$(__DS), %ax
		movw	%ax, %ds	
		movl %esp, %eax
		
		pushl %eax
		pushl	$0x&vector&
		call	runtime_idtexceptionhandler
		addl  $0x08, %esp
		
		popa
		iretl
	
.endm




runtime_emitidtstub 0	
runtime_emitidtstub 1	
runtime_emitidtstub 2	
runtime_emitidtstub 3	
runtime_emitidtstub 4	
runtime_emitidtstub 5	
runtime_emitidtstub 6	
runtime_emitidtstub 7	
runtime_emitidtstub 8	
runtime_emitidtstub 9	
runtime_emitidtstub a	
runtime_emitidtstub b	
runtime_emitidtstub c	
runtime_emitidtstub d	
runtime_emitidtstub e	
runtime_emitidtstub f	
runtime_emitidtstub 10	
runtime_emitidtstub 11	
runtime_emitidtstub 12	
runtime_emitidtstub 13	
runtime_emitidtstub 14	
runtime_emitidtstub 15	
runtime_emitidtstub 16	
runtime_emitidtstub 17	
runtime_emitidtstub 18	
runtime_emitidtstub 19	
runtime_emitidtstub 1a	
runtime_emitidtstub 1b	
runtime_emitidtstub 1c	
runtime_emitidtstub 1d	
runtime_emitidtstub 1e	
runtime_emitidtstub 1f	
//------------------------------------------------------------------------------



	.extern cstartup

	.section .s_init
	//load gdt
	lgdt __runtimegdt
	
	//load segment selectors 
	movw	$(__DS), %ax
	movw	%ax, %ds	
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	movw  %ax, %ss
	ljmp	$(__CS), $(1f)
1:

	//initialize stack
	movl    $(runtime_stack + __RUNTIMESTACK_SIZE), %esp

	//clear flags
	pushl	$0
	popf

  //call C startup
	pushl %edx	//bootmodule1 size
	pushl %ecx	//bootmodule1 start
	pushl %ebx	//bootmodule size
	pushl %esi	//bootmodule start
	call cstartup

	//we should never come here
halt:
	hlt
	jmp halt



.section .data
	__runtimegdt:
	.word	__runtimegdt_end - __runtimegdt_start - 1	
	.long	__runtimegdt_start

	.align	16
	.global __runtimegdt_start
	__runtimegdt_start:
	.quad	0x0000000000000000	
	.quad	0x00cf9a000000ffff	
	.quad	0x00cf92000000ffff	
	.quad	0x0000000000000000	
	__runtimegdt_end:

	.align	16
	.global __runtimeidt
	__runtimeidt:
	.word __runtimeidt_end - __runtimeidt_start - 1
	.long __runtimeidt_start
	.align 16
	.global __runtimeidt_start
	__runtimeidt_start:
	.fill	8*32, 1, 0
	__runtimeidt_end:
	.align 16
	.global __runtimeidt_functionpointers
	__runtimeidt_functionpointers:
	.long runtime_idtstub0
	.long runtime_idtstub1
	.long runtime_idtstub2
	.long runtime_idtstub3
	.long runtime_idtstub4
	.long runtime_idtstub5
	.long runtime_idtstub6
	.long runtime_idtstub7
	.long runtime_idtstub8
	.long runtime_idtstub9
	.long runtime_idtstuba
	.long runtime_idtstubb
	.long runtime_idtstubc
	.long runtime_idtstubd
	.long runtime_idtstube
	.long runtime_idtstubf
	.long runtime_idtstub10
	.long runtime_idtstub11
	.long runtime_idtstub12
	.long runtime_idtstub13
	.long runtime_idtstub14
	.long runtime_idtstub15
	.long runtime_idtstub16
	.long runtime_idtstub17
	.long runtime_idtstub18
	.long runtime_idtstub19
	.long runtime_idtstub1a
	.long runtime_idtstub1b
	.long runtime_idtstub1c
	.long runtime_idtstub1d
	.long runtime_idtstub1e
	.long runtime_idtstub1f


	.section .stack
	.global runtime_stack
	runtime_stack:
	.fill	__RUNTIMESTACK_SIZE, 1, 0
	
	.section .vmxdata
	.global __runtimetss
	__runtimetss:
	.fill	__RUNTIMETSS_SIZE, 1, 0
	__runtimetss_end:

	.global __runtime_pdpt
	__runtime_pdpt:
	.fill 4096, 1, 0
	.global __runtime_pdts
	__runtime_pdts:
	.fill 4096*4, 1, 0
	
	.global __runtime_reachregion
	__runtime_reachregion:
	.fill 0x10000, 1, 0
	
