#include <target.h>

	.section .multiboot_header

	.align 4
	.global multiboot_header
multiboot_header:
	.long 0x1BADB002
	.long 0x10003
	.long	-(0x1BAEB005) 
	.long multiboot_header
	.long multiboot_header
	.long 0
	.long 0
	.long loader_start
	.long 0
	.long 0
	.long 0
	.long 0
	
	.extern cstartup
	.section .text
	.global loader_start
loader_start:
	//setup our stack
	movl    $(loader_stack + __LOADERSTACK_SIZE), %esp

	//clear flags     
  pushl   $0
  popf
     
  //call C startup with multiboot bootloader parameters
  pushl   %ebx
  pushl   %eax
	call cstartup
	
	//we should never come here
halt:
	hlt
	jmp halt
	
	
	.section .stack
	.global loader_stack
	loader_stack:
	.fill	__LOADERSTACK_SIZE, 1, 0
	
