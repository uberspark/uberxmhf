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
	
	movl    $(loader_stack + 8192), %esp
     
  pushl   $0
  popf
     
  pushl   %ebx
  pushl   %eax
     
	call cstartup
	
halt:
	hlt
	jmp halt
	
//------------------------------------------------------------------------------	
	.global XtLdrTransferControlToRtm
XtLdrTransferControlToRtm:
//------------------------------------------------------------------------------
	movl 	0x4(%esp), %esi
	movl 	0x8(%esp), %edi

	subl  0x8, %esp
	
	movw  (%esi), %ax
	movw  %ax, (%esp)
	movl  0x2(%esi), %eax
	movl  %eax, 0x2(%esp)
	
	lgdt	(%esp)

	movw  (%edi), %ax
	movw  %ax, (%esp)
	movl  0x2(%edi), %eax
	movl  %eax, 0x2(%esp)
	
	lidt	(%esp)

	addl  0x8, %esp
	
	movw	$(__DS), %ax
	movw	%ax, %ds	
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	ljmp	$(__CS), $(1f)
1:

	pushl	$0
	popf

	movl 	0xC(%esp), %edi
	movl  0x10(%esp), %esi
	
	movl  %esi,  %esp
	
	jmpl *%edi
	
	
//---spinlock/unlock------------------------------------------------------------
.section .text
  .global spin_lock
  spin_lock:
    pushl %esi
    movl 0x8(%esp), %esi
    spin:	bt	$0, (%esi)		//mutex is available?
      	jnc	spin			      //wait till it is

      	lock				        //lock the bus (exclusive access)	
	      btr	$0, (%esi)		    //and try to grab the mutex	
	      jnc	spin			      //spin until successful --> spinlock :p
    popl %esi
    ret
    
  .global spin_unlock
  spin_unlock:
      pushl %esi
      movl 0x8(%esp), %esi
      bts	$0, (%esi)		       //release the spinlock
      popl %esi
      ret
	
	.section .stack
	.global loader_stack
loader_stack:
	.fill	8192, 1, 0
	
