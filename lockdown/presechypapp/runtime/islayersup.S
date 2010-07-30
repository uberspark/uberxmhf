//------------------------------------------------------------------------------
// islayersup.S
//
// intel VT isolation layer data/stubs
//
// author: amit vasudevan (amitvasudevan@acm.org)
#include <target.h>

	.extern vt_intercepthandler
	.extern vt_handleerror
	.extern results
	.extern rocount
	.extern info_vminstr_error
	.extern machine
	.extern elements

.section .data
	.align	128
	.global vmx_invalidate_descriptor
	vmx_invalidate_descriptor:
	.word	0
	.word 0
	.long 0
	.long 0
	.long 0
	

	
.section .text
	//.global vmx_invalidate
	//vmx_invalidate:
	//pushl %eax
	//pushl %ebx
	//leal vmx_invalidate_descriptor, %ebx
	//movl $1, %eax
	//invvpid (%ecx), %eax 
	//jbe	vt_vmfail
	//popl %eax
	//ret
	

	.global __islayer_callback
	__islayer_callback:
		movl %eax, guest_RAX
		movl %ebx, guest_RBX
		movl %ecx, guest_RCX
		movl %edx, guest_RDX
		movl %ebp, guest_RBP
		movl %esi, guest_RSI
		movl %edi, guest_RDI
		
		movl %cr2, %eax
		movl %eax, guest_CR2
		
		//store VMCS from CPU into our memory variables
		read:
			xor %edx, %edx
			mov rocount, %ecx
			nxrd:
				mov results+0(%edx), %eax
				mov results+4(%edx), %ebx
				vmread %eax, (%ebx)
				jbe vt_vmfail
				add $8, %edx
				loop nxrd

		read_1:
			xor %edx, %edx
			mov elements, %ecx
			nxrd_1:
				mov machine+0(%edx), %eax
				mov machine+4(%edx), %ebx
				vmread %eax, (%ebx)
				jbe vt_vmfail
				add $8, %edx
				loop nxrd_1
			
	  call vt_intercepthandler
	  
		//write our memory variables to CPU VMCS
		xor	%edx, %edx
		mov	elements, %ecx
		lt_0:					
			mov	machine+0(%edx), %eax
			mov	machine+4(%edx), %ebx
		  vmwrite (%ebx), %eax
			jbe	vt_vmfail
		  add	$8, %edx
		  loop	lt_0
	  
	  movl guest_CR2, %eax
	  movl %eax, %cr2
	  
	  mov guest_RAX, %eax
	  mov guest_RBX, %ebx
	  mov guest_RCX, %ecx
	  mov guest_RDX, %edx
	  mov guest_RBP, %ebp
	  mov guest_RSI, %esi
	  mov guest_RDI, %edi
	  
		vmresume
		.global vt_vmfail
		vt_vmfail:
			jc failInvalid
		failValid:
			movl $0x4400, %eax
			lea info_vminstr_error, %ebx
			vmread %eax, (%ebx)
		failInvalid:
			call vt_handleerror
			ud2 //we never come here

.section .vmxdata
	.global __limbo_gdt
	__limbo_gdt:
	.fill	__LIMBO_GDT_SIZE, 1, 0

	.global __limbo_tss
	__limbo_tss:
	.fill	__LIMBO_TSS_SIZE, 1, 0
	
	.global __ept_pml4_table
	__ept_pml4_table:
	.fill 4096, 1, 0
	
	.global __ept_pdp_table
	__ept_pdp_table:
	.fill 4096, 1, 0
	
	.global __ept_pd_tables
	__ept_pd_tables:
	.fill 4096*4, 1, 0
	
	.global __ept_p_tables
	__ept_p_tables:
	.fill 2048*4096, 1, 0
	
	.global __msr_area_host
	__msr_area_host:
	.fill	8192, 1, 0
	
	.global __msr_area_guest
	__msr_area_guest:
	.fill	8192, 1, 0
	
	.global __vmx_io_bitmap
	__vmx_io_bitmap:
	.fill 8192, 1, 0
	
	
	//shadow page tables (PAE mode)
	.global __shadow_pdp_table
	__shadow_pdp_table:
	.fill 4096, 1, 0
	
	.global __shadow_pd_tables
	__shadow_pd_tables:
	.fill (4*4096), 1, 0
	
	.global __shadow_p_tables
	__shadow_p_tables:
	.fill (2048*4096), 1, 0
	
	//shadow page tables (non-PAE mode)
	.global __shadow_npae_pd_table
	__shadow_npae_pd_table:
	.fill 4096, 1, 0
	
	.global __shadow_npae_p_tables
	__shadow_npae_p_tables:
	.fill 1024*4096, 1, 0
	
	//shadow page tables (alg0 mode)
	.global __shadow_alg0_area
	__shadow_alg0_area:
	.fill 4096*256, 1, 0
	
	