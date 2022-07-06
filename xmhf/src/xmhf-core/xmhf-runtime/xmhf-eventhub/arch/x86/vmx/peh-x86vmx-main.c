/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

// peh-x86vmx-main.c
// EMHF partition event-hub for Intel x86 vmx
// author: amit vasudevan (amitvasudevan@acm.org)
#include <xmhf.h>


//---VMX decode assist----------------------------------------------------------
//map a CPU register index into appropriate VCPU *vcpu or struct regs *r field
//and return the address of the field
#ifdef __AMD64__
static uintptr_t * _vmx_decode_reg(u32 gpr, VCPU *vcpu, struct regs *r){
    switch(gpr){
        case  0: return &r->rax;
        case  1: return &r->rcx;
        case  2: return &r->rdx;
        case  3: return &r->rbx;
        case  4: return (u64*)&vcpu->vmcs.guest_RSP;
        case  5: return &r->rbp;
        case  6: return &r->rsi;
        case  7: return &r->rdi;
        case  8: return &r->r8 ;
        case  9: return &r->r9 ;
        case 10: return &r->r10;
        case 11: return &r->r11;
        case 12: return &r->r12;
        case 13: return &r->r13;
        case 14: return &r->r14;
        case 15: return &r->r15;
        default: {
            printf("[%02x]%s: invalid gpr value (%u). halting!\n", vcpu->id,
                   __FUNCTION__, gpr);
            HALT();
            //we will never get here, appease the compiler
            return (u64 *)&r->rax;
        }
    }
}
#elif defined(__I386__)
static uintptr_t * _vmx_decode_reg(u32 gpr, VCPU *vcpu, struct regs *r){
  if ( ((int)gpr >=0) && ((int)gpr <= 7) ){

	  switch(gpr){
		case 0: return ( (u32 *)&r->eax );
		case 1: return ( (u32 *)&r->ecx );
		case 2: return ( (u32 *)&r->edx );
		case 3: return ( (u32 *)&r->ebx );
		case 4: return ( (u32 *)&vcpu->vmcs.guest_RSP);
		case 5: return ( (u32 *)&r->ebp );
		case 6: return ( (u32 *)&r->esi );
		case 7: return ( (u32 *)&r->edi );
	  }
   }else{
		printf("[%02x]%s: invalid gpr value (%u). halting!\n", vcpu->id,
			__FUNCTION__, gpr);
		HALT();
   }

	//we will never get here, appease the compiler
	return (u32 *)&r->eax;
}
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */

/*
 * Inject an exception to guest
 *
 * The interception handler should return soon after calling this function.
 * Especially, guest RIP should not be increased.
 *
 * vector: exception vector
 * has_ec: whether the exception has error code (0 or 1)
 * errcode: value of error code
 */
void _vmx_inject_exception(VCPU *vcpu, u32 vector, u32 has_ec, u32 errcode)
{
	union {
		struct _vmx_event_injection st;
		uint32_t ui;
	} injection_info;
	HALT_ON_ERRORCOND(vector < 32);
	HALT_ON_ERRORCOND(has_ec <= 1);
	injection_info.ui = 0;
	injection_info.st.vector = vector;  /* e.g. #UD, #GP */
	injection_info.st.type = 0x3;       /* Hardware Exception */
	injection_info.st.errorcode = has_ec;
	injection_info.st.valid = 1;
	vcpu->vmcs.control_VM_entry_interruption_information = injection_info.ui;
	vcpu->vmcs.control_VM_entry_exception_errorcode = errcode;
}

u64 _vmx_get_guest_efer(VCPU *vcpu)
{
	msr_entry_t *efer = &((msr_entry_t *)vcpu->vmx_vaddr_msr_area_guest)[0];
	HALT_ON_ERRORCOND(efer->index == MSR_EFER);
	return efer->data;
}


//---intercept handler (CPUID)--------------------------------------------------
static void _vmx_handle_intercept_cpuid(VCPU *vcpu, struct regs *r){
	//printf("CPU(0x%02x): CPUID\n", vcpu->id);
	u32 old_eax = r->eax;
	asm volatile ("cpuid\r\n"
          :"=a"(r->eax), "=b"(r->ebx), "=c"(r->ecx), "=d"(r->edx)
          :"a"(r->eax), "c" (r->ecx));
	
	// Use the registers returned by <xmhf_app_handlecpuid>
	xmhf_app_handlecpuid(vcpu, r, old_eax);

	if (old_eax == 0x1U) {
		/* Clear VMX capability */
		r->ecx &= ~(1U << 5);
#ifdef __HIDE_X2APIC__
		/* Clear x2APIC capability (not stable in Circle CI and HP 840) */
		r->ecx &= ~(1U << 21);
#endif /* __HIDE_X2APIC__ */
#ifndef __UPDATE_INTEL_UCODE__
		/*
		 * Set Hypervisor Present bit.
		 * Fedora 35's AP will retry updating Intel microcode forever if the
		 * update fails. So we set the hypervisor present bit to work around
		 * this problem.
		 */
		r->ecx |= (1U << 31);
#endif /* !__UPDATE_INTEL_UCODE__ */
	}
#ifdef __I386__
	/*
	 * For i386 XMHF running on an AMD64 CPU, make the guest think that the CPU
	 * is i386 (i.e. 32-bits).
	 */
	if (old_eax == 0x80000001U) {
		r->edx &= ~(1U << 29);
	}
#elif !defined(__AMD64__)
    #error "Unsupported Arch"
#endif /* !defined(__AMD64__) */
	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
}


//---vmx int 15 intercept handler-----------------------------------------------
static void _vmx_int15_handleintercept(VCPU *vcpu, struct regs *r){
	u16 cs, ip;
	u8 *bdamemory = (u8 *)0x4AC;

	//if in V86 mode translate the virtual address to physical address
	if( (vcpu->vmcs.guest_CR0 & CR0_PE) && (vcpu->vmcs.guest_CR0 & CR0_PG) &&
			(vcpu->vmcs.guest_RFLAGS & EFLAGS_VM) ){
		u8 *bdamemoryphysical;
		#ifdef __XMHF_VERIFICATION__
			bdamemoryphysical = (u8 *)nondet_u32();
		#else
			bdamemoryphysical = (u8 *)xmhf_smpguest_arch_x86vmx_walk_pagetables(vcpu, (hva_t)bdamemory);
		#endif
		if((sla_t)bdamemoryphysical < rpb->XtVmmRuntimePhysBase){
			printf("INT15 (E820): V86 mode, bdamemory translated from %08lx to %08lx\n",
				(hva_t)bdamemory, (sla_t)bdamemoryphysical);
			bdamemory = bdamemoryphysical;
		}else{
			printf("CPU(0x%02x): INT15 (E820) V86 mode, translated bdamemory points beyond \
				guest physical memory space. Halting!\n", vcpu->id);
			HALT();
		}
	}


	//if E820 service then...
	if((u16)r->eax == 0xE820){
		//AX=0xE820, EBX=continuation value, 0 for first call
		//ES:DI pointer to buffer, ECX=buffer size, EDX='SMAP'
		//return value, CF=0 indicated no error, EAX='SMAP'
		//ES:DI left untouched, ECX=size returned, EBX=next continuation value
		//EBX=0 if last descriptor
		printf("CPU(0x%02x): INT 15(e820): EDX=0x%08x, EBX=0x%08x, ECX=0x%08x, ES=0x%04x, DI=0x%04x\n",
		vcpu->id, (u16)r->eax, r->edx, r->ebx, r->ecx, (u16)vcpu->vmcs.guest_ES_selector, (u16)r->edi);

		//HALT_ON_ERRORCOND(r->edx == 0x534D4150UL);  //'SMAP' should be specified by guest
		//HALT_ON_ERRORCOND(r->ebx < rpb->XtVmmE820NumEntries); //invalid continuation value specified by guest!
		if( (r->edx == 0x534D4150UL) && (r->ebx < rpb->XtVmmE820NumEntries) ){

			//copy the e820 descriptor and return its size in ECX
			{

				if( ((sla_t)(vcpu->vmcs.guest_ES_base+(u16)r->edi)) < rpb->XtVmmRuntimePhysBase){
					GRUBE820 *pe820entry;
					#ifdef __XMHF_VERIFICATION__
						GRUBE820 e820entry;
						pe820entry = &e820entry;
					#else
						pe820entry = (GRUBE820 *)((sla_t)(vcpu->vmcs.guest_ES_base+(u16)r->edi));
					#endif //__XMHF_VERIFICATION__
					pe820entry->baseaddr_low = g_e820map[r->ebx].baseaddr_low;
					pe820entry->baseaddr_high = g_e820map[r->ebx].baseaddr_high;
					pe820entry->length_low = g_e820map[r->ebx].length_low;
					pe820entry->length_high = g_e820map[r->ebx].length_high;
					pe820entry->type = g_e820map[r->ebx].type;
					/*
					 * 64-bit: Check whether exceed supported memory.
					 * 32-bit: Continue even if machine has physical memory > 4G
					 */
#ifdef __AMD64__
					{
						u64 baseaddr = (((u64)pe820entry->baseaddr_high) << 32) |
										pe820entry->baseaddr_low;
						u64 length = (((u64)pe820entry->length_high) << 32) |
									pe820entry->length_low;
						HALT_ON_ERRORCOND(baseaddr + length <= MAX_PHYS_ADDR);
					}
#elif !defined(__I386__)
    #error "Unsupported Arch"
#endif /* !defined(__I386__) */
				}else{
					printf("CPU(0x%02x): INT15 E820. Guest buffer is beyond guest "
							"physical memory bounds. Halting!\n", vcpu->id);
					HALT();
				}

			}
			r->ecx=20;

			//set EAX to 'SMAP' as required by the service call
			r->eax=r->edx;

			//we need to update carry flag in the guest EFLAGS register
			//however since INT 15 would have pushed the guest FLAGS on stack
			//we cannot simply reflect the change by modifying vmcb->rflags
			//instead we need to make the change to the pushed FLAGS register on
			//the guest stack. the real-mode IRET frame looks like the following
			//when viewed at top of stack
			//guest_ip		(16-bits)
			//guest_cs		(16-bits)
			//guest_flags (16-bits)
			//...

			{
				//u16 guest_cs, guest_ip, guest_flags;
				u16 guest_cs __attribute__((unused)), guest_ip __attribute__((unused)), guest_flags;
				/* Truncate RSP to 16 bits, (higher bits not used in real mode) */
				u16 *gueststackregion = (u16 *)( (hva_t)vcpu->vmcs.guest_SS_base + (u16)vcpu->vmcs.guest_RSP );


				//if V86 mode translate the virtual address to physical address
				if( (vcpu->vmcs.guest_CR0 & CR0_PE) && (vcpu->vmcs.guest_CR0 & CR0_PG) &&
					(vcpu->vmcs.guest_RFLAGS & EFLAGS_VM) ){
					#ifdef __XMHF_VERIFICATION__
						u8 *gueststackregionphysical = (u8 *)nondet_u32();
					#else
						u8 *gueststackregionphysical = (u8 *)xmhf_smpguest_arch_x86vmx_walk_pagetables(vcpu, (hva_t)gueststackregion);
					#endif
					if((sla_t)gueststackregionphysical < rpb->XtVmmRuntimePhysBase){
						printf("INT15 (E820): V86 mode, gueststackregion translated from 0x%08lx to 0x%08lx\n",
							(hva_t)gueststackregion, (sla_t)gueststackregionphysical);
						gueststackregion = (u16 *)gueststackregionphysical;
					}else{
						printf("CPU(0x%02x): INT15 (E820) V86 mode, translated gueststackregion points beyond \
							guest physical memory space. Halting!\n", vcpu->id);
						HALT();
					}
				}


				//get guest IP, CS and FLAGS from the IRET frame
				#ifdef __XMHF_VERIFICATION__
					guest_ip = nondet_u16();
					guest_cs = nondet_u16();
					guest_flags = nondet_u16();
				#else
					guest_ip = gueststackregion[0];
					guest_cs = gueststackregion[1];
					guest_flags = gueststackregion[2];
				#endif	//__XMHF_VERIFICATION__


				//increment e820 descriptor continuation value
				r->ebx=r->ebx+1;
				if (r->ebx >= rpb->XtVmmE820NumEntries) {
					//we have reached the last record, so make EBX=0
					r->ebx=0;
				}

				// clear CF when success
				guest_flags &= ~(u16)EFLAGS_CF;
				#ifndef __XMHF_VERIFICATION__
					gueststackregion[2] = guest_flags;
				#endif

			}

		}else{	//invalid state specified during INT 15 E820, fail by
				//setting carry flag
				printf("CPU(0x%02x): INT15 (E820), invalid state specified by guest \
						Halting!\n", vcpu->id);
				HALT();
		}

		//update RIP to execute the IRET following the VMCALL instruction
		//effectively returning from the INT 15 call made by the guest
		vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;

		return;
	} //E820 service

	//ok, this is some other INT 15h service, so simply chain to the original
	//INT 15h handler

#ifdef __XMHF_VERIFICATION__
	//get IP and CS of the original INT 15h handler
	ip = nondet_u16();
	cs = nondet_u16();
#else
	//get IP and CS of the original INT 15h handler
	ip = *((u16 *)((hva_t)bdamemory + 4));
	cs = *((u16 *)((hva_t)bdamemory + 6));
#endif

	//update VMCS with the CS and IP and let go
	vcpu->vmcs.guest_RIP = ip;
	vcpu->vmcs.guest_CS_base = cs * 16;
	vcpu->vmcs.guest_CS_selector = cs;
}




//------------------------------------------------------------------------------
// guest MSR r/w intercept handling
// HAL invokes NT kernel via SYSENTER if CPU supports it. However,
// regular apps using NTDLL will still use INT 2E if registry entry is not
// tweaked. So, we HAVE to emulate SYSENTER_CS/EIP/ESP to ensure that
// NT kernel doesnt panic with SESSION5_INITIALIZATION_FAILED!
//
// This took me nearly a month of disassembly into the HAL,
// NTKERNEL and debugging to figure out..eh?
//
// AMD SVM is neater, only
// when you ask for these MSR intercepts do they get stored and read from
// the VMCB. However, for Intel regardless they get stored and read from VMCS
// for the guest. So we need to have these intercepts bare minimum!!
// A line to this effect would have been much appreciated in the Intel manuals
// doh!!!
//------------------------------------------------------------------------------

/*
 * Simulate guest writing a MSR with ecx=index, value=edx:eax
 *
 * The MSRs that will be changed by VMENTRY/VMEXIT MSR load/store are not
 * supported: MSR_EFER, MSR_IA32_PAT, MSR_K6_STAR
 *
 * Return 0 if success, 1 if failure (should inject #GP to guest)
 */
u32 xmhf_parteventhub_arch_x86vmx_handle_wrmsr(VCPU *vcpu, u32 index, u64 value)
{
	switch (index) {
		case MSR_EFER: /* fallthrough */
		case MSR_IA32_PAT: /* fallthrough */
		case MSR_K6_STAR:
			HALT_ON_ERRORCOND(0 && "Illegal behavior");
			break;
		case IA32_SYSENTER_CS_MSR:
			vcpu->vmcs.guest_SYSENTER_CS = (u32)value;
			break;
		case IA32_SYSENTER_EIP_MSR:
			vcpu->vmcs.guest_SYSENTER_EIP = (u64)value;
			break;
		case IA32_SYSENTER_ESP_MSR:
			vcpu->vmcs.guest_SYSENTER_ESP = (u64)value;
			break;
		case IA32_MSR_FS_BASE:
			vcpu->vmcs.guest_FS_base = (u64)value;
			break;
		case IA32_MSR_GS_BASE:
			vcpu->vmcs.guest_GS_base = (u64)value;
			break;
		case IA32_MTRRCAP: /* fallthrough */
		case IA32_MTRR_DEF_TYPE: /* fallthrough */
		case IA32_MTRR_FIX64K_00000: /* fallthrough */
		case IA32_MTRR_FIX16K_80000: /* fallthrough */
		case IA32_MTRR_FIX16K_A0000: /* fallthrough */
		case IA32_MTRR_FIX4K_C0000: /* fallthrough */
		case IA32_MTRR_FIX4K_C8000: /* fallthrough */
		case IA32_MTRR_FIX4K_D0000: /* fallthrough */
		case IA32_MTRR_FIX4K_D8000: /* fallthrough */
		case IA32_MTRR_FIX4K_E0000: /* fallthrough */
		case IA32_MTRR_FIX4K_E8000: /* fallthrough */
		case IA32_MTRR_FIX4K_F0000: /* fallthrough */
		case IA32_MTRR_FIX4K_F8000: /* fallthrough */
		case IA32_MTRR_PHYSBASE0: /* fallthrough */
		case IA32_MTRR_PHYSMASK0: /* fallthrough */
		case IA32_MTRR_PHYSBASE1: /* fallthrough */
		case IA32_MTRR_PHYSMASK1: /* fallthrough */
		case IA32_MTRR_PHYSBASE2: /* fallthrough */
		case IA32_MTRR_PHYSMASK2: /* fallthrough */
		case IA32_MTRR_PHYSBASE3: /* fallthrough */
		case IA32_MTRR_PHYSMASK3: /* fallthrough */
		case IA32_MTRR_PHYSBASE4: /* fallthrough */
		case IA32_MTRR_PHYSMASK4: /* fallthrough */
		case IA32_MTRR_PHYSBASE5: /* fallthrough */
		case IA32_MTRR_PHYSMASK5: /* fallthrough */
		case IA32_MTRR_PHYSBASE6: /* fallthrough */
		case IA32_MTRR_PHYSMASK6: /* fallthrough */
		case IA32_MTRR_PHYSBASE7: /* fallthrough */
		case IA32_MTRR_PHYSMASK7: /* fallthrough */
		case IA32_MTRR_PHYSBASE8: /* fallthrough */
		case IA32_MTRR_PHYSMASK8: /* fallthrough */
		case IA32_MTRR_PHYSBASE9: /* fallthrough */
		case IA32_MTRR_PHYSMASK9:
			/*
			 * Need to change EPT to reflect MTRR changes, because host MTRRs
			 * are not used when EPT is used.
			 */
			if (xmhf_memprot_arch_x86vmx_mtrr_write(vcpu, index, value)) {
				/*
				 * When designed, xmhf_memprot_arch_x86vmx_mtrr_write() has not
				 * been observed to fail. This may happen if the guest OS
				 * performs an invalid WRMSR. Please make sure that in this
				 * case injecting #GP is the correct action.
				 */
				HALT_ON_ERRORCOND(0 && "Unexperienced fail in MTRR write");
				return 1;
			}
			break;
		case IA32_BIOS_UPDT_TRIG:
#ifdef __UPDATE_INTEL_UCODE__
			printf("CPU(0x%02x): OS tries to write microcode!\n", vcpu->id);
			printf("gva for microcode update: 0x%016llx\n", value);
			handle_intel_ucode_update(vcpu, value);
#else /* !__UPDATE_INTEL_UCODE__ */
			printf("CPU(0x%02x): OS tries to write microcode, ignore\n",
					vcpu->id);
#endif /* __UPDATE_INTEL_UCODE__ */
			break;
		case IA32_X2APIC_ICR:
			if (xmhf_smpguest_arch_x86vmx_eventhandler_x2apic_icrwrite(vcpu, value) == 0) {
				/* Forward to physical APIC */
				wrmsr64(index, value);
			}
			break;
		default:{
			wrmsr64(index, value);
			break;
		}
	}
	return 0;
}

//---intercept handler (WRMSR)--------------------------------------------------
static void _vmx_handle_intercept_wrmsr(VCPU *vcpu, struct regs *r){
	u64 write_data = ((u64)r->edx << 32) | (u64)r->eax;

	//printf("CPU(0x%02x): WRMSR 0x%08x 0x%08x%08x @ %p\n", vcpu->id, r->ecx, r->edx, r->eax, vcpu->vmcs.guest_RIP);

	switch(r->ecx){
		case MSR_EFER: /* fallthrough */
		case MSR_IA32_PAT: /* fallthrough */
		case MSR_K6_STAR: {
			u32 found = 0;
            u32 i = 0;
			for (i = 0; i < vcpu->vmcs.control_VM_entry_MSR_load_count; i++) {
				msr_entry_t *entry = &((msr_entry_t *)vcpu->vmx_vaddr_msr_area_guest)[i];
				if (entry->index == r->ecx) {
					entry->data = write_data;
					found = 1;
					break;
				}
			}
			HALT_ON_ERRORCOND(found != 0);
			break;
		}
		default:
			if (xmhf_parteventhub_arch_x86vmx_handle_wrmsr(vcpu, r->ecx, write_data)) {
				_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
				return;
			}
	}

	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	//printf("CPU(0x%02x): WRMSR end\n", vcpu->id);
	return;
}

/*
 * Simulate guest reading a MSR with ecx=index. *value will become edx:eax
 *
 * The MSRs that will be changed by VMENTRY/VMEXIT MSR load/store are not
 * supported: MSR_EFER, MSR_IA32_PAT, MSR_K6_STAR
 *
 * Return 0 if success, 1 if failure (should inject #GP to guest)
 */
u32 xmhf_parteventhub_arch_x86vmx_handle_rdmsr(VCPU *vcpu, u32 index, u64 *value)
{
	switch (index) {
		case MSR_EFER: /* fallthrough */
		case MSR_IA32_PAT: /* fallthrough */
		case MSR_K6_STAR:
			HALT_ON_ERRORCOND(0 && "Illegal behavior");
			break;
		case IA32_SYSENTER_CS_MSR:
			*value = (u64)vcpu->vmcs.guest_SYSENTER_CS;
			break;
		case IA32_SYSENTER_EIP_MSR:
			*value = (u64)vcpu->vmcs.guest_SYSENTER_EIP;
			break;
		case IA32_SYSENTER_ESP_MSR:
			*value = (u64)vcpu->vmcs.guest_SYSENTER_ESP;
			break;
		case IA32_MSR_FS_BASE:
			*value = (u64)vcpu->vmcs.guest_FS_base;
			break;
		case IA32_MSR_GS_BASE:
			*value = (u64)vcpu->vmcs.guest_GS_base;
			break;
		case IA32_MTRR_DEF_TYPE: /* fallthrough */
		case IA32_MTRR_FIX64K_00000: /* fallthrough */
		case IA32_MTRR_FIX16K_80000: /* fallthrough */
		case IA32_MTRR_FIX16K_A0000: /* fallthrough */
		case IA32_MTRR_FIX4K_C0000: /* fallthrough */
		case IA32_MTRR_FIX4K_C8000: /* fallthrough */
		case IA32_MTRR_FIX4K_D0000: /* fallthrough */
		case IA32_MTRR_FIX4K_D8000: /* fallthrough */
		case IA32_MTRR_FIX4K_E0000: /* fallthrough */
		case IA32_MTRR_FIX4K_E8000: /* fallthrough */
		case IA32_MTRR_FIX4K_F0000: /* fallthrough */
		case IA32_MTRR_FIX4K_F8000: /* fallthrough */
		case IA32_MTRR_PHYSBASE0: /* fallthrough */
		case IA32_MTRR_PHYSMASK0: /* fallthrough */
		case IA32_MTRR_PHYSBASE1: /* fallthrough */
		case IA32_MTRR_PHYSMASK1: /* fallthrough */
		case IA32_MTRR_PHYSBASE2: /* fallthrough */
		case IA32_MTRR_PHYSMASK2: /* fallthrough */
		case IA32_MTRR_PHYSBASE3: /* fallthrough */
		case IA32_MTRR_PHYSMASK3: /* fallthrough */
		case IA32_MTRR_PHYSBASE4: /* fallthrough */
		case IA32_MTRR_PHYSMASK4: /* fallthrough */
		case IA32_MTRR_PHYSBASE5: /* fallthrough */
		case IA32_MTRR_PHYSMASK5: /* fallthrough */
		case IA32_MTRR_PHYSBASE6: /* fallthrough */
		case IA32_MTRR_PHYSMASK6: /* fallthrough */
		case IA32_MTRR_PHYSBASE7: /* fallthrough */
		case IA32_MTRR_PHYSMASK7: /* fallthrough */
		case IA32_MTRR_PHYSBASE8: /* fallthrough */
		case IA32_MTRR_PHYSMASK8: /* fallthrough */
		case IA32_MTRR_PHYSBASE9: /* fallthrough */
		case IA32_MTRR_PHYSMASK9:
			/*
			 * When reading MTRR MSRs, IA32_MTRRCAP is the same as host's MSR.
			 * Other MTRR MSRs come from the shadow in vcpu.
			 */
			if (xmhf_memprot_arch_x86vmx_mtrr_read(vcpu, index, value)) {
				/*
				 * When designed, xmhf_memprot_arch_x86vmx_mtrr_read() cannot
				 * fail. Please make sure injecting #GP is the correct action.
				 */
				HALT_ON_ERRORCOND(0 && "Unexpected fail in MTRR read");
				return 1;
			}
			break;
		case IA32_X2APIC_ICR:
			// TODO: we can probably just forward it to hardware x2APIC
			HALT_ON_ERRORCOND(0 && "TODO: x2APIC ICR read not implemented");
			break;
		default:{
			if (rdmsr_safe(index, value) != 0) {
				return 1;
			}
			break;
		}
	}
	return 0;
}

//---intercept handler (RDMSR)--------------------------------------------------
static void _vmx_handle_intercept_rdmsr(VCPU *vcpu, struct regs *r){
	/* After switch statement, will assign this value to r->eax and r->edx */
	u64 read_result = 0;

	//printf("CPU(0x%02x): RDMSR 0x%08x @ %p\n", vcpu->id, r->ecx, vcpu->vmcs.guest_RIP);

	switch(r->ecx){
		case MSR_EFER: /* fallthrough */
		case MSR_IA32_PAT: /* fallthrough */
		case MSR_K6_STAR: {
			u32 found = 0;
            u32 i = 0;
			for (i = 0; i < vcpu->vmcs.control_VM_exit_MSR_store_count; i++) {
				msr_entry_t *entry = &((msr_entry_t *)vcpu->vmx_vaddr_msr_area_guest)[i];
				if (entry->index == r->ecx) {
					read_result = entry->data;
					found = 1;
					break;
				}
			}
			HALT_ON_ERRORCOND(found != 0);
			break;
		}
		default:
			if (xmhf_parteventhub_arch_x86vmx_handle_rdmsr(vcpu, r->ecx, &read_result)) {
				_vmx_inject_exception(vcpu, CPU_EXCEPTION_GP, 1, 0);
				return;
			}
			break;
	}

	/* Assign read_result to r->eax and r->edx */
	{
#ifdef __AMD64__
		r->rax = 0;	/* Clear upper 32-bits of RAX */
		r->rdx = 0;	/* Clear upper 32-bits of RDX */
#elif !defined(__I386__)
    #error "Unsupported Arch"
#endif /* !defined(__I386__) */
		r->eax = (u32)(read_result);
		r->edx = (u32)(read_result >> 32);
	}

	//printf("CPU(0x%02x): RDMSR (0x%08x)=0x%08x%08x\n", vcpu->id, r->ecx, r->edx, r->eax);

	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
	return;
}


//---intercept handler (EPT voilation)----------------------------------
static void _vmx_handle_intercept_eptviolation(VCPU *vcpu, struct regs *r){
	ulong_t errorcode;
	uintptr_t gva;
	u64 gpa;
	errorcode = (ulong_t)vcpu->vmcs.info_exit_qualification;
	gpa = vcpu->vmcs.guest_paddr;
	gva = (uintptr_t)vcpu->vmcs.info_guest_linear_address;

	//check if EPT violation is due to LAPIC interception
	if(vcpu->isbsp && (gpa >= g_vmx_lapic_base) && (gpa < (g_vmx_lapic_base + PAGE_SIZE_4K)) ){
		xmhf_smpguest_arch_x86_eventhandler_hwpgtblviolation(vcpu, (u32)gpa, errorcode);
	}else{ //no, pass it to hypapp
		xmhf_smpguest_arch_x86vmx_quiesce(vcpu);
		xmhf_app_handleintercept_hwpgtblviolation(vcpu, r, gpa, gva,
				(errorcode & 7));
		xmhf_smpguest_arch_x86vmx_endquiesce(vcpu);
	}
}


//---intercept handler (I/O port access)----------------------------------------
static void _vmx_handle_intercept_ioportaccess(VCPU *vcpu, struct regs *r){
  u32 access_size, access_type, portnum, stringio;
	u32 app_ret_status = APP_IOINTERCEPT_CHAIN;

  access_size = (u32)vcpu->vmcs.info_exit_qualification & 0x00000007UL;
	access_type = ((u32)vcpu->vmcs.info_exit_qualification & 0x00000008UL) >> 3;
	portnum =  ((u32)vcpu->vmcs.info_exit_qualification & 0xFFFF0000UL) >> 16;
	stringio = ((u32)vcpu->vmcs.info_exit_qualification & 0x00000010UL) >> 4;

  HALT_ON_ERRORCOND(!stringio);	//we dont handle string IO intercepts

  //call our app handler, TODO: it should be possible for an app to
  //NOT want a callback by setting up some parameters during appmain
	xmhf_smpguest_arch_x86vmx_quiesce(vcpu);
	app_ret_status=xmhf_app_handleintercept_portaccess(vcpu, r, portnum, access_type,
          access_size);
    xmhf_smpguest_arch_x86vmx_endquiesce(vcpu);

  if(app_ret_status == APP_IOINTERCEPT_CHAIN){
   	if(access_type == IO_TYPE_OUT){
  		if( access_size== IO_SIZE_BYTE)
  				outb((u8)r->eax, portnum);
  		else if (access_size == IO_SIZE_WORD)
  				outw((u16)r->eax, portnum);
  		else if (access_size == IO_SIZE_DWORD)
  				outl((u32)r->eax, portnum);
  	}else{
  		if( access_size== IO_SIZE_BYTE){
  				r->eax &= 0xFFFFFF00UL;	//clear lower 8 bits
  				r->eax |= (u8)inb(portnum);
  		}else if (access_size == IO_SIZE_WORD){
  				r->eax &= 0xFFFF0000UL;	//clear lower 16 bits
  				r->eax |= (u16)inw(portnum);
  		}else if (access_size == IO_SIZE_DWORD){
  				r->eax = (u32)inl(portnum);
  		}
  	}
  	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;

  }else{
    //skip the IO instruction, app has taken care of it
  	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
  }

	return;
}


//---CR0 access handler-------------------------------------------------
static void vmx_handle_intercept_cr0access_ug(VCPU *vcpu, struct regs *r, u32 gpr, u32 tofrom){
	ulong_t cr0_value, old_cr0, old_cr0_shadow;
	ulong_t fixed_1_fields;

	HALT_ON_ERRORCOND(tofrom == VMX_CRX_ACCESS_TO);

	cr0_value = *((uintptr_t *)_vmx_decode_reg(gpr, vcpu, r));
	old_cr0 = vcpu->vmcs.guest_CR0;
	old_cr0_shadow = vcpu->vmcs.control_CR0_shadow;

	//printf("[cr0-%02x] MOV TO, old=0x%08lx, new=0x%08lx, shadow=0x%08lx\n",
	//	vcpu->id, old_cr0, cr0_value, old_cr0_shadow);

	/*
	 * Make the guest think that move to CR0 succeeds (by changing shadow).
	 *
	 * control_CR0_mask is set in vmx_initunrestrictedguestVMCS(). The mask
	 * is the IA32_VMX_CR0_FIXED0 MSR, with PE and PG unset, CD and NW set.
	 *
	 * Intel manual says that exceptions to fixed CR0 are CD NW PG PE.
	 *
	 * So for all set bits in control_CR0_mask, we force CD and NW to be not
	 * set, and other bits to be set.
	 */

	fixed_1_fields = vcpu->vmcs.control_CR0_mask;
	vcpu->vmcs.control_CR0_shadow = cr0_value;
	vcpu->vmcs.guest_CR0 = (cr0_value | fixed_1_fields) & ~(CR0_CD | CR0_NW);

	/*
	 * If CR0.PG, need to update a lot of things for PAE and long mode support.
	 * As a workaround, we let the guest retry setting CR0.PG and CR0.PE. This
	 * way we do not need to calculate the VMCS fields in hypervisor.
	 */
	if ((old_cr0 ^ cr0_value) & CR0_PG) {
		ulong_t pg_pe_mask = (CR0_PG | CR0_PE);
		/* Make sure that CR0.PG and CR0.PE are not masked */
		if (!(pg_pe_mask & vcpu->vmcs.control_CR0_mask)) {
			/*
			 * The original MOV CR0 must also change some bits in CR0 mask
			 * (not related to CR0.PG or CR0.PE due to previous check).
			 */
			HALT_ON_ERRORCOND((old_cr0_shadow ^ cr0_value) &
							  vcpu->vmcs.control_CR0_mask);
			/*
			 * Change VMCS's guest CR0 to requested value, except CR0.PG and
			 * CR0.PE.
			 */
			vcpu->vmcs.guest_CR0 &= ~pg_pe_mask;
			vcpu->vmcs.guest_CR0 |= old_cr0 & pg_pe_mask;
			//printf("[cr0-%02x] RETRY:  old=0x%08lx\n", vcpu->id,
			//	vcpu->vmcs.guest_CR0);
			/* Sanity check: for bits masked, requested value = CR0 shadow */
			HALT_ON_ERRORCOND(
				((cr0_value ^ vcpu->vmcs.control_CR0_shadow) &
				vcpu->vmcs.control_CR0_mask) == 0);
			/*
			 * Sanity check: for bits not masked other than CR0.PG and CR0.PE,
			 * guest CR0 = requested new value.
			 */
			HALT_ON_ERRORCOND(
				((vcpu->vmcs.guest_CR0 ^ cr0_value) &
				~vcpu->vmcs.control_CR0_mask & ~pg_pe_mask) == 0);
			/* Skip incrementing PC (RIP / EIP), retry this instruction */
			return;
		}
	}

	/*
	 * If CR0.PG bit changes, need to update guest_PDPTE0 - guest_PDPTE3 if
	 * PAE is enabled.
	 *
	 * x86 XMHF cannot support PAE guests easily because the hypervisor cannot
	 * access memory above 4GB.
	 *
	 * To support amd64 guests, also need to update bit 9 of VM-Entry Controls
	 * (IA-32e mode guest). This bit should always equal to EFER.LME && CR0.PG
	 */
	if ((old_cr0 ^ cr0_value) & CR0_PG) {
#ifdef __AMD64__
		u32 value = vcpu->vmcs.control_VM_entry_controls;
		u32 lme, pae;
		u64 efer = _vmx_get_guest_efer(vcpu);
		lme = (cr0_value & CR0_PG) && (efer & (1U << EFER_LME));
		value &= ~(1U << VMX_VMENTRY_IA_32E_MODE_GUEST);
		value |= lme << VMX_VMENTRY_IA_32E_MODE_GUEST;
		vcpu->vmcs.control_VM_entry_controls = value;
		pae = (cr0_value & CR0_PG) && (!lme) && (vcpu->vmcs.guest_CR4 & CR4_PAE);
#elif defined(__I386__)
		u32 pae = (cr0_value & CR0_PG) && (vcpu->vmcs.guest_CR4 & CR4_PAE);
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
		/* If PAE, need to walk EPT and retrieve values for guest_PDPTE* */
		if (pae) {
			guestmem_hptw_ctx_pair_t ctx_pair;
			u64 pdptes[4];
			u64 addr = vcpu->vmcs.guest_CR3 & ~0x1FUL;
			guestmem_init(vcpu, &ctx_pair);
			guestmem_copy_gp2h(&ctx_pair, 0, pdptes, addr, sizeof(pdptes));
			vcpu->vmcs.guest_PDPTE0 = pdptes[0];
			vcpu->vmcs.guest_PDPTE1 = pdptes[1];
			vcpu->vmcs.guest_PDPTE2 = pdptes[2];
			vcpu->vmcs.guest_PDPTE3 = pdptes[3];
		}
	}

	//flush mappings
	xmhf_memprot_arch_x86vmx_flushmappings(vcpu);

	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
}

//---CR4 access handler---------------------------------------------------------
static void vmx_handle_intercept_cr4access_ug(VCPU *vcpu, struct regs *r, u32 gpr, u32 tofrom){
  if(tofrom == VMX_CRX_ACCESS_TO){
	ulong_t cr4_proposed_value;

	cr4_proposed_value = *((uintptr_t *)_vmx_decode_reg(gpr, vcpu, r));

	printf("CPU(0x%02x): CS:RIP=0x%04x:0x%08lx MOV CR4, xx\n", vcpu->id,
			(u32)vcpu->vmcs.guest_CS_selector, vcpu->vmcs.guest_RIP);

	printf("MOV TO CR4 (flush TLB?), current=0x%08lx, proposed=0x%08lx\n",
			vcpu->vmcs.guest_CR4, cr4_proposed_value);

	/*
	 * CR4 mask is the IA32_VMX_CR4_FIXED0 MSR. Modify CR4 shadow to let the
	 * guest think MOV CR4 succeeds.
	 */
	vcpu->vmcs.control_CR4_shadow = cr4_proposed_value;
	vcpu->vmcs.guest_CR4 = (cr4_proposed_value | vcpu->vmcs.control_CR4_mask);

	#if defined (__NESTED_PAGING__)
	//we need to flush EPT mappings as we emulated CR4 load above
	HALT_ON_ERRORCOND(__vmx_invvpid(VMX_INVVPID_SINGLECONTEXT, 1, 0));
	#endif
  }

  vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
}

//---XSETBV intercept handler-------------------------------------------
static void _vmx_handle_intercept_xsetbv(VCPU *vcpu, struct regs *r){
	u64 xcr_value;

	xcr_value = ((u64)r->edx << 32) + (u64)r->eax;

	if(r->ecx != XCR_XFEATURE_ENABLED_MASK){
			printf("%s: unhandled XCR register %u\n", __FUNCTION__, r->ecx);
			HALT();
	}

	//XXX: TODO: check for invalid states and inject GP accordingly

	printf("%s: xcr_value=0x%llx\n", __FUNCTION__, xcr_value);

	//XXX: debug: dump CR4 contents
	{
		ulong_t t_cr4;
		t_cr4 = read_cr4();
		printf("%s: host cr4 value=0x%08lx\n", __FUNCTION__, t_cr4);
	}

	//set XCR with supplied value
	xsetbv(XCR_XFEATURE_ENABLED_MASK, xcr_value);

	//skip the emulated XSETBV instruction
	vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
}


#ifdef __OPTIMIZE_NESTED_VIRT__

/*
 * Optimize xmhf_parteventhub_arch_x86vmx_intercept_handler for some frequently
 * used intercepts observed in real operating systems. This reduces number of
 * VMREAD / VMWRITE during the intercepts and speeds up when XMHF is running in
 * a hypervisor.
 *
 * The optimizations depend on the logic in the specific handlers. For example,
 * if _vmx_handle_intercept_cpuid() accesses more VMCS fields, then the
 * optimization may become incorrect.
 *
 * Return 1 if optimized, or 0 if not optimized.
 */
static u32 _optimize_x86vmx_intercept_handler(VCPU *vcpu, struct regs *r){
	vcpu->vmcs.info_vmexit_reason = __vmx_vmread32(0x4402);

	switch ((u32)vcpu->vmcs.info_vmexit_reason) {
	case VMX_VMEXIT_WRMSR:
		/* Only optimize WRMSR for some MSRs */
		switch (r->ecx) {
		case 0x6e0:	/* IA32_TSC_DEADLINE */
			/* fallthrough */
		case 0x80b:	/* IA32_X2APIC_EOI */
			vcpu->vmcs.guest_RIP = __vmx_vmreadNW(0x681E);
			vcpu->vmcs.info_vmexit_instruction_length = __vmx_vmread32(0x440C);
			_vmx_handle_intercept_wrmsr(vcpu, r);
			__vmx_vmwriteNW(0x681E, vcpu->vmcs.guest_RIP);
			return 1;
		default:
			return 0;
		}
	case VMX_VMEXIT_CPUID:
		/* Always optimize CPUID */
		vcpu->vmcs.guest_RIP = __vmx_vmreadNW(0x681E);
		vcpu->vmcs.info_vmexit_instruction_length = __vmx_vmread32(0x440C);
		_vmx_handle_intercept_cpuid(vcpu, r);
		__vmx_vmwriteNW(0x681E, vcpu->vmcs.guest_RIP);
		return 1;
	case VMX_VMEXIT_EPT_VIOLATION: {
		/* Optimize EPT violation due to LAPIC */
		u64 gpa;
		vcpu->vmcs.guest_paddr = __vmx_vmread64(0x2400);
		gpa = vcpu->vmcs.guest_paddr;
		if(vcpu->isbsp && (gpa >= g_vmx_lapic_base) && (gpa < (g_vmx_lapic_base + PAGE_SIZE_4K)) ){
			vcpu->vmcs.info_exit_qualification = __vmx_vmreadNW(0x6400);
			vcpu->vmcs.control_exception_bitmap = __vmx_vmread32(0x4004);
			vcpu->vmcs.guest_interruptibility = __vmx_vmread32(0x4824);
			vcpu->vmcs.guest_RFLAGS = __vmx_vmreadNW(0x6820);
			vcpu->vmcs.control_EPT_pointer = __vmx_vmread64(0x201A);
			_vmx_handle_intercept_eptviolation(vcpu, r);
			__vmx_vmwrite32(0x4004, vcpu->vmcs.control_exception_bitmap);
			__vmx_vmwrite32(0x4824, vcpu->vmcs.guest_interruptibility);
			__vmx_vmwriteNW(0x6820, vcpu->vmcs.guest_RFLAGS);
			return 1;
		}
		return 0;
	}
	case VMX_VMEXIT_EXCEPTION:
		/* Optimize debug exception (#DB) for LAPIC operation */
		vcpu->vmcs.info_vmexit_interrupt_information = __vmx_vmread32(0x4404);
		if (((u32)vcpu->vmcs.info_vmexit_interrupt_information &
			 INTR_INFO_VECTOR_MASK) == 1) {
			vcpu->vmcs.guest_CS_selector = __vmx_vmread16(0x0802);
			vcpu->vmcs.guest_RIP = __vmx_vmreadNW(0x681E);
			vcpu->vmcs.control_exception_bitmap = __vmx_vmread32(0x4004);
			vcpu->vmcs.guest_interruptibility = __vmx_vmread32(0x4824);
			vcpu->vmcs.guest_RFLAGS = __vmx_vmreadNW(0x6820);
			vcpu->vmcs.control_EPT_pointer = __vmx_vmread64(0x201A);
			xmhf_smpguest_arch_x86_eventhandler_dbexception(vcpu, r);
			__vmx_vmwrite32(0x4004, vcpu->vmcs.control_exception_bitmap);
			__vmx_vmwrite32(0x4824, vcpu->vmcs.guest_interruptibility);
			__vmx_vmwriteNW(0x6820, vcpu->vmcs.guest_RFLAGS);
			return 1;
		}
		return 0;
	default:
		return 0;
	}
}

#endif /* __OPTIMIZE_NESTED_VIRT__ */

u32 xmhf_parteventhub_arch_x86vmx_print_guest(VCPU *vcpu, struct regs *r)
{
	(void)r;

#ifdef __AMD64__
	if (vcpu->vmcs.control_VM_entry_controls & (1U << VMX_VMENTRY_IA_32E_MODE_GUEST)) 
	{
		// amd64 mode
		printf("	CPU(0x%02x): RFLAGS=0x%016lx\n",
				vcpu->id, vcpu->vmcs.guest_RFLAGS);
		printf("	SS:RSP =0x%04x:0x%016lx\n",
				(u16)vcpu->vmcs.guest_SS_selector,
				vcpu->vmcs.guest_RSP);
		printf("	CS:RIP =0x%04x:0x%016lx\n",
				(u16)vcpu->vmcs.guest_CS_selector,
				vcpu->vmcs.guest_RIP);
		printf("	IDTR base:limit=0x%016lx:0x%04x\n",
				vcpu->vmcs.guest_IDTR_base,
				(u16)vcpu->vmcs.guest_IDTR_limit);
		printf("	GDTR base:limit=0x%016lx:0x%04x\n",
				vcpu->vmcs.guest_GDTR_base,
				(u16)vcpu->vmcs.guest_GDTR_limit);
		if(vcpu->vmcs.info_IDT_vectoring_information & 0x80000000){
			printf("CPU(0x%02x): HALT; Nested events unhandled 0x%08x\n",
				vcpu->id, vcpu->vmcs.info_IDT_vectoring_information);
		}
		HALT();
	}

#elif !defined(__I386__)
	#error "Unsupported Arch"
#endif /* !defined(__I386__) */
	// i386 mode
	printf("	CPU(0x%02x): EFLAGS=0x%08lx\n",
			vcpu->id, (u32)vcpu->vmcs.guest_RFLAGS);
	printf("	SS:ESP =0x%04x:0x%08lx\n",
			(u16)vcpu->vmcs.guest_SS_selector,
			(u32)vcpu->vmcs.guest_RSP);
	printf("	CS:EIP =0x%04x:0x%08lx\n",
			(u16)vcpu->vmcs.guest_CS_selector,
			(u32)vcpu->vmcs.guest_RIP);
	printf("	IDTR base:limit=0x%08lx:0x%04x\n",
			(u32)vcpu->vmcs.guest_IDTR_base,
			(u16)vcpu->vmcs.guest_IDTR_limit);
	printf("	GDTR base:limit=0x%08lx:0x%04x\n",
			(u32)vcpu->vmcs.guest_GDTR_base,
			(u16)vcpu->vmcs.guest_GDTR_limit);
	if(vcpu->vmcs.info_IDT_vectoring_information & 0x80000000){
		printf("CPU(0x%02x): HALT; Nested events unhandled 0x%08x\n",
			vcpu->id, vcpu->vmcs.info_IDT_vectoring_information);
	}
	HALT();
}

//---hvm_intercept_handler------------------------------------------------------
u32 xmhf_parteventhub_arch_x86vmx_intercept_handler(VCPU *vcpu, struct regs *r){
#ifdef __OPTIMIZE_NESTED_VIRT__
	if (_optimize_x86vmx_intercept_handler(vcpu, r)) {
		return 1;
	}
#endif /* __OPTIMIZE_NESTED_VIRT__ */
	//read VMCS from physical CPU/core
#ifndef __XMHF_VERIFICATION__
	/*
	 * Logic to handle asynchronous access to vcpu->vmcs.control_VMX_cpu_based.
	 * See xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception().
	 */
	vcpu->vmx_guest_vmcs_nmi_window_set = false;
	vcpu->vmx_guest_vmcs_nmi_window_clear = false;
	vcpu->vmx_guest_nmi_blocking_modified = false;
	xmhf_baseplatform_arch_x86vmx_getVMCS(vcpu);
#endif //__XMHF_VERIFICATION__
	//sanity check for VM-entry errors
	if( (u32)vcpu->vmcs.info_vmexit_reason & 0x80000000UL ){
		printf("CPU(0x%02x): VM-ENTRY error: reason=0x%08x, qualification=0x%016llx\n",
			vcpu->id, (u32)vcpu->vmcs.info_vmexit_reason,
			(u64)vcpu->vmcs.info_exit_qualification);
		xmhf_baseplatform_arch_x86vmx_dump_vcpu(vcpu);
		HALT();
	}

	/*
	 * Cannot print anything before event handler returns if this intercept
	 * is for quiescing (vcpu->vmcs.info_vmexit_reason == VMX_VMEXIT_EXCEPTION),
	 * otherwise will deadlock. See xmhf_smpguest_arch_x86vmx_quiesce().
	 */
//	if (vcpu->vmcs.info_vmexit_reason != VMX_VMEXIT_EXCEPTION) {
//		printf("{%d,%d}", vcpu->id, (u32)vcpu->vmcs.info_vmexit_reason);
//	}

	//handle intercepts
	switch((u32)vcpu->vmcs.info_vmexit_reason){
		//--------------------------------------------------------------
		//xmhf-core and hypapp intercepts
		//--------------------------------------------------------------

		case VMX_VMEXIT_VMCALL:{
			//if INT 15h E820 hypercall, then let the xmhf-core handle it
			if(vcpu->vmcs.guest_CS_base == (VMX_UG_E820HOOK_CS << 4) &&
				vcpu->vmcs.guest_RIP == VMX_UG_E820HOOK_IP){
				//we need to be either in real-mode or in protected
				//mode with paging and EFLAGS.VM bit set (virtual-8086 mode)
				HALT_ON_ERRORCOND( !(vcpu->vmcs.guest_CR0 & CR0_PE)  ||
					( (vcpu->vmcs.guest_CR0 & CR0_PE) && (vcpu->vmcs.guest_CR0 & CR0_PG) &&
						(vcpu->vmcs.guest_RFLAGS & EFLAGS_VM)  ) );
				_vmx_int15_handleintercept(vcpu, r);
			}else{	//if not E820 hook, give hypapp a chance to handle the hypercall
				xmhf_smpguest_arch_x86vmx_quiesce(vcpu);
				if( xmhf_app_handlehypercall(vcpu, r) != APP_SUCCESS){
					printf("CPU(0x%02x): error(halt), unhandled hypercall 0x%08x!\n", vcpu->id, r->eax);
					HALT();
				}
				xmhf_smpguest_arch_x86vmx_endquiesce(vcpu);
				vcpu->vmcs.guest_RIP += vcpu->vmcs.info_vmexit_instruction_length;
			}
		}
		break;

		case VMX_VMEXIT_IOIO:{
			_vmx_handle_intercept_ioportaccess(vcpu, r);
		}
		break;

		case VMX_VMEXIT_EPT_VIOLATION:{
			_vmx_handle_intercept_eptviolation(vcpu, r);
		}
		break;

		case VMX_VMEXIT_INIT:{
			printf("***** VMEXIT_INIT xmhf_runtime_shutdown\n\n");
			xmhf_runtime_shutdown(vcpu, r);
			printf("CPU(0x%02x): Fatal, xmhf_runtime_shutdown returned. Halting!\n", vcpu->id);
			HALT();
		}
		break;

		//--------------------------------------------------------------
		//xmhf-core only intercepts
		//--------------------------------------------------------------
		case VMX_VMEXIT_HLT:
			if(!vcpu->vmx_guest_unrestricted){
				printf("CPU(0x%02x): V86 monitor based real-mode exec. unsupported!\n", vcpu->id);
				HALT();
			}else{
				printf("CPU(0x%02x): Unexpected HLT intercept in UG, Halting!\n", vcpu->id);
				HALT();
			}
		break;

 		case VMX_VMEXIT_EXCEPTION:{
			switch( ((u32)vcpu->vmcs.info_vmexit_interrupt_information & INTR_INFO_VECTOR_MASK) ){
				case 0x01:
					xmhf_smpguest_arch_x86_eventhandler_dbexception(vcpu, r);
					break;

				case 0x02:	//NMI
					#ifndef __XMHF_VERIFICATION__
					//we currently discharge quiescing via manual inspection
					xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(vcpu, r, 1);
					#endif // __XMHF_VERIFICATION__
					break;

				default:
					printf("VMEXIT-EXCEPTION:\n");
					printf("control_exception_bitmap=0x%08x\n",
						vcpu->vmcs.control_exception_bitmap);
					printf("interruption information=0x%08x\n",
						vcpu->vmcs.info_vmexit_interrupt_information);
					printf("errorcode=0x%08x\n",
						vcpu->vmcs.info_vmexit_interrupt_error_code);

					xmhf_parteventhub_arch_x86vmx_print_guest(vcpu, r);
					HALT();
			}
		}
		break;

		case VMX_VMEXIT_NMI_WINDOW: {
			/* Clear NMI windowing */
			vcpu->vmcs.control_VMX_cpu_based &= ~(1U << VMX_PROCBASED_NMI_WINDOW_EXITING);
			/* Check whether the CPU can handle NMI */
			if (vcpu->vmcs.control_exception_bitmap & (1U << CPU_EXCEPTION_NMI)) {
				/*
				 * TODO: hypapp has chosen to intercept NMI so callback.
				 * Currently not implemented. One way is to drop the NMI
				 * interrupt.
				 *
				 * For example, TrustVisor should use VCPU_gnmiblock_set() to
				 * block NMIs when running PALs. For now, halt to make sure
				 * hypapp developer notices the problem.
				 */
				printf("CPU(0x%02x): HALT because dropping NMI\n", vcpu->id);
				HALT_ON_ERRORCOND(0);
			} else {
				/* Inject NMI to guest */
                vcpu->vmcs.control_VM_entry_exception_errorcode = 0;
                vcpu->vmcs.control_VM_entry_interruption_information = NMI_VECTOR |
                    INTR_TYPE_NMI |
                    INTR_INFO_VALID_MASK;
                vcpu->vmx_guest_nmi_cfg.guest_nmi_pending = false;
                printf("CPU(0x%02x): inject NMI\n", vcpu->id);
			}
		}
		break;

 		case VMX_VMEXIT_CRX_ACCESS:{
			u32 tofrom, gpr, crx;
			//printf("VMEXIT_CRX_ACCESS:\n");
			//printf("instruction length: %u\n", info_vmexit_instruction_length);
			crx=(u32) ((u64)vcpu->vmcs.info_exit_qualification & 0x000000000000000FULL);
			gpr=
			 (u32) (((u64)vcpu->vmcs.info_exit_qualification & 0x0000000000000F00ULL) >> (u64)8);
			tofrom =
			(u32) (((u64)vcpu->vmcs.info_exit_qualification & 0x0000000000000030ULL) >> (u64)4);
			//printf("crx=%u, gpr=%u, tofrom=%u\n", crx, gpr, tofrom);

#ifdef __AMD64__
			if ( ((int)gpr >=0) && ((int)gpr <= 15) ){
#elif defined(__I386__)
			if ( ((int)gpr >=0) && ((int)gpr <= 7) ){
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
				switch(crx){
					case 0x0: //CR0 access
						vmx_handle_intercept_cr0access_ug(vcpu, r, gpr, tofrom);
						break;

					case 0x4: //CR4 access
						if(!vcpu->vmx_guest_unrestricted){
							printf("HALT: v86 monitor based real-mode exec. unsupported!\n");
							HALT();
						}else{
							vmx_handle_intercept_cr4access_ug(vcpu, r, gpr, tofrom);
						}
						break;

					default:
						printf("unhandled crx, halting!\n");
						HALT();
				}
			}else{
				printf("[%02x]%s: invalid gpr value (%u). halting!\n", vcpu->id,
					__FUNCTION__, gpr);
				HALT();
			}
		}
		break;

 		case VMX_VMEXIT_RDMSR:
			_vmx_handle_intercept_rdmsr(vcpu, r);
			break;

		case VMX_VMEXIT_WRMSR:
			_vmx_handle_intercept_wrmsr(vcpu, r);
			break;

		case VMX_VMEXIT_CPUID:
			_vmx_handle_intercept_cpuid(vcpu, r);
			break;

		case VMX_VMEXIT_TASKSWITCH:{
			u32 idt_v = vcpu->vmcs.info_IDT_vectoring_information & VECTORING_INFO_VALID_MASK;
			u32 type = vcpu->vmcs.info_IDT_vectoring_information & VECTORING_INFO_TYPE_MASK;
			u32 reason = vcpu->vmcs.info_exit_qualification >> 30;
			u16 tss_selector = (u16)vcpu->vmcs.info_exit_qualification;

			if(reason == TASK_SWITCH_GATE && type == INTR_TYPE_NMI){
				printf("CPU(0x%02x): NMI received (MP guest shutdown?)\n", vcpu->id);
					xmhf_runtime_shutdown(vcpu, r);
				printf("CPU(0x%02x): warning, xmhf_runtime_shutdown returned!\n", vcpu->id);
				printf("CPU(0x%02x): HALTING!\n", vcpu->id);
				HALT();
			}else{
				printf("CPU(0x%02x): Unhandled Task Switch. Halt!\n", vcpu->id);
				printf("	idt_v=0x%08x, type=0x%08x, reason=0x%08x, tsssel=0x%04x\n",
					idt_v, type, reason, tss_selector);
			}
			HALT();
		}
		break;

		case VMX_VMEXIT_XSETBV:{
			_vmx_handle_intercept_xsetbv(vcpu, r);
		}
		break;


		default:{
			printf("CPU(0x%02x): Unhandled intercept: %d (0x%08x)\n",
					vcpu->id, vcpu->vmcs.info_vmexit_reason,
					vcpu->vmcs.info_vmexit_reason);
			xmhf_parteventhub_arch_x86vmx_print_guest(vcpu, r);
			HALT();
		}
	} //end switch((u32)vcpu->vmcs.info_vmexit_reason)


	/*
	 * Check and clear guest interruptibility state.
	 * However, ignore bit 3, because it is for virtual NMI.
	 */
	if ((vcpu->vmcs.guest_interruptibility & ~(1U << 3)) != 0){
		vcpu->vmcs.guest_interruptibility &= (1U << 3);
	}

	//make sure we have no nested events
	if(vcpu->vmcs.info_IDT_vectoring_information & 0x80000000){
		printf("CPU(0x%02x): HALT; Nested events unhandled with hwp:0x%08x\n",
			vcpu->id, vcpu->vmcs.info_IDT_vectoring_information);
		HALT();
	}

	//write updated VMCS back to CPU
#ifndef __XMHF_VERIFICATION__
	xmhf_baseplatform_arch_x86vmx_putVMCS(vcpu);
	/*
	 * Logic to handle asynchronous access to vcpu->vmcs.control_VMX_cpu_based.
	 * See xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception().
	 */
	if (vcpu->vmx_guest_vmcs_nmi_window_set) {
		u32 __control_VMX_cpu_based = __vmx_vmread32(0x4002);
		__control_VMX_cpu_based |= (1U << VMX_PROCBASED_NMI_WINDOW_EXITING);
		__vmx_vmwrite32(0x4002, __control_VMX_cpu_based);
	}
	if (vcpu->vmx_guest_vmcs_nmi_window_clear) {
		u32 __control_VMX_cpu_based = __vmx_vmread32(0x4002);
		__control_VMX_cpu_based &= ~(1U << VMX_PROCBASED_NMI_WINDOW_EXITING);
		__vmx_vmwrite32(0x4002, __control_VMX_cpu_based);
	}
#endif // __XMHF_VERIFICATION__


#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
	//ensure that whenever a partition is resumed on a vcpu, we have extended paging
	//enabled and that the base points to the extended page tables we have initialized
	assert( (vcpu->vmcs.control_VMX_seccpu_based & (1U << VMX_SECPROCBASED_ENABLE_EPT)) );
	assert( (vcpu->vmcs.control_EPT_pointer == (hva2spa((void*)vcpu->vmx_vaddr_ept_pml4_table) | 0x1E)) );
#endif

	return 1;
}
