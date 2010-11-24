// secure loader low-level support routines
// authors: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>
#include <msr.h>
#include <svm.h>

.section .text
//------------------------------------------------------------------------------	
	.global XtLdrTransferControlToRtm
XtLdrTransferControlToRtm:
//------------------------------------------------------------------------------
	movl 	0x4(%esp), %esi
	movl 	0x8(%esp), %edi

	subl  $0x8, %esp
	
	movw  %fs:(%esi), %ax
	movw  %ax, (%esp)
	movl  %fs:0x2(%esi), %eax
	movl  %eax, 0x2(%esp)

	lgdt	(%esp)

	movw  %fs:(%edi), %ax
	movw  %ax, (%esp)
	movl  %fs:0x2(%edi), %eax
	movl  %eax, 0x2(%esp)
	
	lidt	(%esp)

	addl  $0x8, %esp
	
	movl 	0xC(%esp), %edi
	movl  0x10(%esp), %esi

	movw	$(__DS), %ax
	movw	%ax, %ds	
	movw	%ax, %es
	movw	%ax, %fs
	movw	%ax, %gs
	
	movw  %ax, %ss
  movl  %esi,%esp

	pushl	$0
	popf
	
	
	int $0x03
//we will patch the entrypoint to the hypervisor runtime before
//transfering control. not the most elegant approach, but since our
//sl CS is segmented, the flat runtime CS can only be reloaded with
//a far selector:offset jump and x86 doesnt have an indirect variant
//of this instruction 
.global	sl_runtime_entrypoint_patch
	sl_runtime_entrypoint_patch:	
	jmp $(__CS), $(0x00000000)

