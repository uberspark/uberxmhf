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

// smpg-x86vmx - EMHF SMP guest component x86 (VMX) backend
// implementation
// author: amit vasudevan (amitvasudevan@acm.org)
#include <xmhf.h>

//the LAPIC register that is being accessed during emulation
static u32 g_vmx_lapic_reg __attribute__(( section(".data") )) = 0;

//the LAPIC operation that is being performed during emulation
static u32 g_vmx_lapic_op __attribute__(( section(".data") )) = LAPIC_OP_RSVD;

//guest TF and IF bit values during LAPIC emulation
static u32 g_vmx_lapic_guest_eflags_tfifmask __attribute__(( section(".data") )) = 0;

//guest "Blocking by NMI" bit in Interruptibility State, for LAPIC interception
static u32 g_vmx_lapic_guest_intr_nmimask __attribute__(( section(".data") )) = 0;

//guest exception bitmap during LAPIC emulation
static u32 g_vmx_lapic_exception_bitmap __attribute__(( section(".data") )) = 0;

/*
 * xmhf_smpguest_arch_x86vmx_quiesce() needs to access printf locks defined
 * in xmhfc-putchar.c
 */
extern void *emhfc_putchar_linelock_arg;
extern void emhfc_putchar_linelock(void *arg);
extern void emhfc_putchar_lineunlock(void *arg);

//----------------------------------------------------------------------
//vmx_lapic_changemapping
//change LAPIC mappings to handle SMP guest bootup

#define VMX_LAPIC_MAP			((u64)EPT_PROT_READ | (u64)EPT_PROT_WRITE)
#define VMX_LAPIC_UNMAP			0

static void vmx_lapic_changemapping(VCPU *vcpu, u32 lapic_paddr, u32 new_lapic_paddr, u64 mapflag){
#ifndef __XMHF_VERIFICATION__
  u64 *pts;
  u32 lapic_page;
  u64 value;

  pts = (u64 *)vcpu->vmx_vaddr_ept_p_tables;
  lapic_page=lapic_paddr/PAGE_SIZE_4K;
  value = (u64)new_lapic_paddr | mapflag;

  pts[lapic_page] = value;

  xmhf_memprot_arch_x86vmx_flushmappings(vcpu);
#endif //__XMHF_VERIFICATION__
}
//----------------------------------------------------------------------


//---checks if all logical cores have received SIPI
//returns 1 if yes, 0 if no
static u32 have_all_cores_recievedSIPI(void){
  u32 i;
  VCPU *vcpu;

	//iterate through all logical processors in master-id table
	for(i=0; i < g_midtable_numentries; i++){
  	vcpu = (VCPU *)g_midtable[i].vcpu_vaddr_ptr;
		if(vcpu->isbsp)
			continue;	//BSP does not receive SIPI

		if(!vcpu->sipireceived)
			return 0;	//one or more logical cores have not received SIPI
  }

  return 1;	//all logical cores have received SIPI
}

//---SIPI processing logic------------------------------------------------------
//return 1 if lapic interception has to be discontinued, typically after
//all aps have received their SIPI, else 0
static u32 processSIPI(VCPU *vcpu, u32 icr_low_value, u32 icr_high_value){
  //we assume that destination is always physical and
  //specified via top 8 bits of icr_high_value
  u32 dest_lapic_id;
  VCPU *dest_vcpu = (VCPU *)0;

  HALT_ON_ERRORCOND( (icr_low_value & 0x000C0000) == 0x0 );

  dest_lapic_id= icr_high_value >> 24;

  printf("\nCPU(0x%02x): %s, dest_lapic_id is 0x%02x",
		vcpu->id, __FUNCTION__, dest_lapic_id);

  //find the vcpu entry of the core with dest_lapic_id
  {
    int i;
    for(i=0; i < (int)g_midtable_numentries; i++){
      if(g_midtable[i].cpu_lapic_id == dest_lapic_id){
        dest_vcpu = (VCPU *)g_midtable[i].vcpu_vaddr_ptr;
        HALT_ON_ERRORCOND( dest_vcpu->id == dest_lapic_id );
        break;
      }
    }

    HALT_ON_ERRORCOND( dest_vcpu != (VCPU *)0 );
  }

  printf("\nCPU(0x%02x): found AP to pass SIPI; id=0x%02x, vcpu=0x%08x",
      vcpu->id, dest_vcpu->id, (uintptr_t)dest_vcpu);


  //send the sipireceived flag to trigger the AP to start the HVM
  if(dest_vcpu->sipireceived){
    printf("\nCPU(0x%02x): destination CPU #0x%02x has already received SIPI, ignoring", vcpu->id, dest_vcpu->id);
  }else{
		dest_vcpu->sipivector = (u8)icr_low_value;
  	dest_vcpu->sipireceived = 1;
  	printf("\nCPU(0x%02x): Sent SIPI command to AP, should awaken it!",
               vcpu->id);
  }

	if(have_all_cores_recievedSIPI())
		return 1;	//all cores have received SIPI, we can discontinue LAPIC interception
	else
		return 0;	//some cores are still to receive SIPI, continue LAPIC interception
}



//----------------------------------------------------------------------
//xmhf_smpguest_arch_x86vmx_initialize
//initialize LAPIC interception machinery
//note: called from the BSP
// If more than 1 CPU will be used, set unmaplapic to 1. APIC will be mapped
// When all APs receive SIPI. Otherwise, set unmaplapic to 0 so that APIC will
// not be unmapped.
void xmhf_smpguest_arch_x86vmx_initialize(VCPU *vcpu, u32 unmaplapic){
  u32 eax, edx;

  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  HALT_ON_ERRORCOND( edx == 0 ); //APIC should be below 4G

  g_vmx_lapic_base = eax & 0xFFFFF000UL;
  //printf("\nBSP(0x%02x): LAPIC base=0x%08x", vcpu->id, g_vmx_lapic_base);

  if (unmaplapic) {
    //unmap LAPIC page
    vmx_lapic_changemapping(vcpu, g_vmx_lapic_base, g_vmx_lapic_base, VMX_LAPIC_UNMAP);
  }
}
//----------------------------------------------------------------------





#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
	bool g_vmx_lapic_npf_verification_guesttrapping = false;
	bool g_vmx_lapic_npf_verification_pre = false;
#endif
//----------------------------------------------------------------------
//xmhf_smpguest_arch_x86vmx_eventhandler_hwpgtblviolation
//handle LAPIC accesses by the guest, used for SMP guest boot
u32 xmhf_smpguest_arch_x86vmx_eventhandler_hwpgtblviolation(VCPU *vcpu, u32 paddr, u32 errorcode){

  //get LAPIC register being accessed
  g_vmx_lapic_reg = (paddr - g_vmx_lapic_base);

#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
  g_vmx_lapic_npf_verification_pre = (errorcode & EPT_ERRORCODE_WRITE) &&
	((g_vmx_lapic_reg == LAPIC_ICR_LOW) || (g_vmx_lapic_reg == LAPIC_ICR_HIGH));
#endif


	if(errorcode & EPT_ERRORCODE_WRITE){			//LAPIC write

		if(g_vmx_lapic_reg == LAPIC_ICR_LOW || g_vmx_lapic_reg == LAPIC_ICR_HIGH ){
			g_vmx_lapic_op = LAPIC_OP_WRITE;
			vmx_lapic_changemapping(vcpu, g_vmx_lapic_base, hva2spa(&g_vmx_virtual_LAPIC_base), VMX_LAPIC_MAP);
		}else{
			g_vmx_lapic_op = LAPIC_OP_RSVD;
			vmx_lapic_changemapping(vcpu, g_vmx_lapic_base, g_vmx_lapic_base, VMX_LAPIC_MAP);
		}

	}else{											//LAPIC read
		if(g_vmx_lapic_reg == LAPIC_ICR_LOW || g_vmx_lapic_reg == LAPIC_ICR_HIGH ){
			g_vmx_lapic_op = LAPIC_OP_READ;
			vmx_lapic_changemapping(vcpu, g_vmx_lapic_base, hva2spa(&g_vmx_virtual_LAPIC_base), VMX_LAPIC_MAP);
		}else{
			g_vmx_lapic_op = LAPIC_OP_RSVD;
			vmx_lapic_changemapping(vcpu, g_vmx_lapic_base, g_vmx_lapic_base, VMX_LAPIC_MAP);
		}
	}

  //save guest IF and TF masks
  g_vmx_lapic_guest_eflags_tfifmask = (u32)vcpu->vmcs.guest_RFLAGS & ((u32)EFLAGS_IF | (u32)EFLAGS_TF);

  //set guest TF
  vcpu->vmcs.guest_RFLAGS |= EFLAGS_TF;

  #ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
	g_vmx_lapic_npf_verification_guesttrapping = true;
  #endif

  //disable interrupts by clearing guest IF on this CPU until we get
  //control in lapic_access_dbexception after a DB exception
  vcpu->vmcs.guest_RFLAGS &= ~(EFLAGS_IF);

  //disable NMIs
  g_vmx_lapic_guest_intr_nmimask = vcpu->vmcs.guest_interruptibility & (1U << 3);
  vcpu->vmcs.guest_interruptibility |= (1U << 3);

  //intercept all exceptions (XMHF will panic if the guest's APIC access resuls
  //in an exception)
  g_vmx_lapic_exception_bitmap = vcpu->vmcs.control_exception_bitmap;
  vcpu->vmcs.control_exception_bitmap = 0xffffffff;

#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
  assert(!g_vmx_lapic_npf_verification_pre || g_vmx_lapic_npf_verification_guesttrapping);
#endif

#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
  assert ( ((g_vmx_lapic_op == LAPIC_OP_RSVD) ||
					   (g_vmx_lapic_op == LAPIC_OP_READ) ||
					   (g_vmx_lapic_op == LAPIC_OP_WRITE))
					 );

  assert ( ((g_vmx_lapic_reg >= 0) &&
					   (g_vmx_lapic_reg < PAGE_SIZE_4K))
					 );
#endif

    return 0; // TODO: currently meaningless
}
//----------------------------------------------------------------------



#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
	bool g_vmx_lapic_db_verification_coreprotected = false;
	bool g_vmx_lapic_db_verification_pre = false;
#endif
//------------------------------------------------------------------------------
//xmhf_smpguest_arch_x86vmx_eventhandler_dbexception
//handle instruction that performed the LAPIC operation
void xmhf_smpguest_arch_x86vmx_eventhandler_dbexception(VCPU *vcpu, struct regs *r){
  u32 delink_lapic_interception=0;

  (void)r;

#ifdef	__XMHF_VERIFICATION_DRIVEASSERTS__
	//this handler relies on two global symbols apart from the parameters, set them
	//to non-deterministic values with correct range
	//note: LAPIC #npf handler ensures this at runtime
	g_vmx_lapic_op = (nondet_u32() % 3) + 1;
	g_vmx_lapic_reg = (nondet_u32() % PAGE_SIZE_4K);
#endif


  if(g_vmx_lapic_op == LAPIC_OP_WRITE){			//LAPIC write
    hva_t src_registeraddress, dst_registeraddress;
    u32 value_tobe_written;

    HALT_ON_ERRORCOND( (g_vmx_lapic_reg == LAPIC_ICR_LOW) || (g_vmx_lapic_reg == LAPIC_ICR_HIGH) );

    src_registeraddress = (hva_t)&g_vmx_virtual_LAPIC_base + g_vmx_lapic_reg;
    dst_registeraddress = (hva_t)g_vmx_lapic_base + g_vmx_lapic_reg;

	#ifdef __XMHF_VERIFICATION__
		//TODO: hardware modeling
		value_tobe_written= nondet_u32();
		#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
		g_vmx_lapic_db_verification_pre = (g_vmx_lapic_op == LAPIC_OP_WRITE) &&
		(g_vmx_lapic_reg == LAPIC_ICR_LOW) &&
		(((value_tobe_written & 0x00000F00) == 0x500) || ( (value_tobe_written & 0x00000F00) == 0x600 ));
		#endif

	#else
		value_tobe_written= *((uintptr_t *)src_registeraddress);
	#endif


    if(g_vmx_lapic_reg == LAPIC_ICR_LOW){
      if ( (value_tobe_written & 0x00000F00) == 0x500){
        //this is an INIT IPI, we just void it
        printf("\n0x%04x:0x%08x -> (ICR=0x%08x write) INIT IPI detected and skipped, value=0x%08x",
          (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP, g_vmx_lapic_reg, value_tobe_written);
        #ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
			g_vmx_lapic_db_verification_coreprotected = true;
		#endif

      }else if( (value_tobe_written & 0x00000F00) == 0x600 ){
        //this is a STARTUP IPI
        u32 icr_value_high = *((u32 *)((hva_t)&g_vmx_virtual_LAPIC_base + (u32)LAPIC_ICR_HIGH));
        printf("\n0x%04x:0x%08x -> (ICR=0x%08x write) STARTUP IPI detected, value=0x%08x",
          (u16)vcpu->vmcs.guest_CS_selector, (u32)vcpu->vmcs.guest_RIP, g_vmx_lapic_reg, value_tobe_written);

		#ifdef __XMHF_VERIFICATION__
			#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
			g_vmx_lapic_db_verification_coreprotected = true;
			#endif
		#else
			delink_lapic_interception=processSIPI(vcpu, value_tobe_written, icr_value_high);
		#endif
      }else{
        #ifndef __XMHF_VERIFICATION__
			//neither an INIT or SIPI, just propagate this IPI to physical LAPIC
			*((u32 *)dst_registeraddress) = value_tobe_written;
		#endif //TODO: hardware modeling
      }
    }else{
       #ifndef __XMHF_VERIFICATION__
			*((u32 *)dst_registeraddress) = value_tobe_written;
	   #endif  //TODO: hardware modeling
    }

  }else if( g_vmx_lapic_op == LAPIC_OP_READ){		//LAPIC read
    hva_t src_registeraddress;
    u32 value_read __attribute__((unused));
    HALT_ON_ERRORCOND( (g_vmx_lapic_reg == LAPIC_ICR_LOW) || (g_vmx_lapic_reg == LAPIC_ICR_HIGH) );

    src_registeraddress = (hva_t)&g_vmx_virtual_LAPIC_base + g_vmx_lapic_reg;

    //TODO: hardware modeling
    #ifndef __XMHF_VERIFICATION__
		value_read = *((u32 *)src_registeraddress);
	#else
		value_read = nondet_u32();
	#endif
  }

  //remove LAPIC interception if all cores have booted up
  if(delink_lapic_interception){
    printf("\n%s: delinking LAPIC interception since all cores have SIPI", __FUNCTION__);
	vmx_lapic_changemapping(vcpu, g_vmx_lapic_base, g_vmx_lapic_base, VMX_LAPIC_MAP);
  }else{
	vmx_lapic_changemapping(vcpu, g_vmx_lapic_base, g_vmx_lapic_base, VMX_LAPIC_UNMAP);
  }

  //restore guest IF and TF
  vcpu->vmcs.guest_RFLAGS &= ~(EFLAGS_IF);
  vcpu->vmcs.guest_RFLAGS &= ~(EFLAGS_TF);
  vcpu->vmcs.guest_RFLAGS |= g_vmx_lapic_guest_eflags_tfifmask;

  //restore NMI blocking (likely enable NMIs)
  vcpu->vmcs.guest_interruptibility |= g_vmx_lapic_guest_intr_nmimask;

  //restore exception bitmap
  vcpu->vmcs.control_exception_bitmap = g_vmx_lapic_exception_bitmap;

#ifdef __XMHF_VERIFICATION_DRIVEASSERTS__
  assert(!g_vmx_lapic_db_verification_pre || g_vmx_lapic_db_verification_coreprotected);
#endif

}

/*
 * This function is called by WRMSR interception where ECX=0x830. Return 1 if
 * smpguest handles this WRMSR. Return 0 if smpguest does not recognize it
 * (should forward the write to physical x2APIC).
 */
int xmhf_smpguest_arch_x86vmx_eventhandler_x2apic_icrwrite(VCPU *vcpu, struct regs *r){
	switch (r->eax & 0x00000F00) {
	case 0x500:
		/* INIT IPI, we just void it */
		printf("\n0x%04x:0x%08llx -> (x2APIC ICR write) INIT IPI skipped, EAX=0x%08x, EDX=0x%08x",
				(u16)vcpu->vmcs.guest_CS_selector, vcpu->vmcs.guest_RIP, r->eax, r->edx);
		return 1;
	case 0x600:
		/* STARTUP IPI */
		printf("\n0x%04x:0x%08llx -> (x2APIC ICR write) STARTUP IPI detected, EAX=0x%08x, EDX=0x%08x",
				(u16)vcpu->vmcs.guest_CS_selector, vcpu->vmcs.guest_RIP, r->eax, r->edx);
		/*
		 * In LAPIC, the destination field is bit 56-63. In x2APIC is 32-63.
		 * As a workaround, we simply left shift the destination field in
		 * x2APIC. The disadvantage is that this only supports 256 LAPIC IDs.
		 */
		HALT_ON_ERRORCOND(r->edx <= 0xff);
		if (processSIPI(vcpu, r->eax, (r->edx << 24))) {
			/*
			 * Ideally the guest should only be using x2APIC and not APIC.
			 * But we nevertheless delink LAPIC interception.
			 */
			printf("\n%s: delinking LAPIC interception since all cores have SIPI", __FUNCTION__);
			vmx_lapic_changemapping(vcpu, g_vmx_lapic_base, g_vmx_lapic_base, VMX_LAPIC_MAP);
		}
		return 1;
	default:
		return 0;
	}
}

//----------------------------------------------------------------------


//----------------------------------------------------------------------
//Queiscing interfaces
//----------------------------------------------------------------------

static void _vmx_send_quiesce_signal(VCPU __attribute__((unused)) *vcpu){
  u32 eax, edx;

  /* Check whether x2APIC is enabled */
  rdmsr(MSR_APIC_BASE, &eax, &edx);

  if (eax & (1U << 10)) {
    /* x2APIC enabled, use it */
    u32 eax = 0x000C0400UL;
    u32 edx = 0xFFFFFFFFUL;
    u32 send_pending;
    wrmsr(IA32_X2APIC_ICR, eax, edx);
    do {
      rdmsr(IA32_X2APIC_ICR, &eax, &edx);
      send_pending = eax & 0x00001000U;
    } while (send_pending);
  } else {
    /* use LAPIC */
    volatile u32 *icr_low = (u32 *)(0xFEE00000 + 0x300);
    volatile u32 *icr_high = (u32 *)(0xFEE00000 + 0x310);
    u32 icr_high_value= 0xFFUL << 24;
    u32 prev_icr_high_value;
    u32 delivered;

    prev_icr_high_value = *icr_high;

    *icr_high = icr_high_value;    //send to all but self
    *icr_low = 0x000C0400UL;      //send NMI

    //check if IPI has been delivered successfully
    //printf("\n%s: CPU(0x%02x): firing NMIs...", __FUNCTION__, vcpu->id);
#ifndef __XMHF_VERIFICATION__
    do {
      // TODO: should this be icr_low?
      delivered = *icr_high;
      delivered &= 0x00001000;
    } while (delivered);
#else
    //TODO: plug in h/w model of LAPIC, for now assume hardware just
    //works
#endif

    //restore icr high
    *icr_high = prev_icr_high_value;
  }

  //printf("\n%s: CPU(0x%02x): NMIs fired!", __FUNCTION__, vcpu->id);
}

/* Unblock NMI by executing iret, but do not jump to somewhere else */
void xmhf_smpguest_arch_x86vmx_unblock_nmi(void) {
#ifdef __AMD64__
    asm volatile (
        "movq    %%rsp, %%rsi   \r\n"
        "xorq    %%rax, %%rax   \r\n"
        "movw    %%ss, %%ax     \r\n"
        "pushq   %%rax          \r\n"
        "pushq   %%rsi          \r\n"
        "pushfq                 \r\n"
        "xorq    %%rax, %%rax   \r\n"
        "movw    %%cs, %%ax     \r\n"
        "pushq   %%rax          \r\n"
        "pushq   $1f            \r\n"
        "iretq                  \r\n"
        "1: nop                 \r\n"
        : // no output
        : // no input
        : "%rax", "%rsi", "cc", "memory");
#elif defined(__I386__)
    asm volatile (
        "pushfl                 \r\n"
        "xorl    %%eax, %%eax   \r\n"
        "movw    %%cs, %%ax     \r\n"
        "pushl   %%eax          \r\n"
        "pushl   $1f            \r\n"
        "iretl                  \r\n"
        "1: nop                 \r\n"
        : // no output
        : // no input
        : "%eax", "cc", "memory");
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
}

//quiesce interface to switch all guest cores into hypervisor mode
//note: we are in atomic processsing mode for this "vcpu"
void xmhf_smpguest_arch_x86vmx_quiesce(VCPU *vcpu){

        //printf("\nCPU(0x%02x): got quiesce signal...", vcpu->id);
        //grab hold of quiesce lock
        spin_lock(&g_vmx_lock_quiesce);
        //printf("\nCPU(0x%02x): grabbed quiesce lock.", vcpu->id);

        /* Acquire the printf lock to prevent deadlock */
        emhfc_putchar_linelock(emhfc_putchar_linelock_arg);

        vcpu->quiesced = 1;
        //reset quiesce counter
        spin_lock(&g_vmx_lock_quiesce_counter);
        g_vmx_quiesce_counter=0;
        spin_unlock(&g_vmx_lock_quiesce_counter);

        //send all the other CPUs the quiesce signal
        g_vmx_quiesce=1;  //we are now processing quiesce
        _vmx_send_quiesce_signal(vcpu);

        //wait for all the remaining CPUs to quiesce
        //printf("\nCPU(0x%02x): waiting for other CPUs to respond...", vcpu->id);
        while(g_vmx_quiesce_counter < (g_midtable_numentries-1) );
        //printf("\nCPU(0x%02x): all CPUs quiesced successfully.", vcpu->id);

        /*
         * Release the printf lock to allow printing things after this function
         * returns.
         *
         * This unlock can be placed either before the while loop for
         * g_vmx_quiesce_counter or after.
         * If unlock after waiting for g_vmx_quiesce_counter, will deadlock if
         * NMI handling code in other CPUs calls printf.
         * If unlock before waiting for g_vmx_quiesce_counter, will deadlock
         * when the other CPUs acquire the lock, and then interrupted by NMI.
         *
         * So in production, should place this unlock after waiting for
         * g_vmx_quiesce_counter. While debugging, if need to use printf in
         * NMI handling code, can change the while loop to release printf lock
         * after a large number of iterations.
         */
        emhfc_putchar_lineunlock(emhfc_putchar_linelock_arg);

}

void xmhf_smpguest_arch_x86vmx_endquiesce(VCPU *vcpu){

        /*
         * g_vmx_quiesce=0 must be before g_vmx_quiesce_resume_signal=1,
         * otherwise if another CPU enters NMI exception handler again,
         * a deadlock may occur.
         */
        g_vmx_quiesce=0;  // we are out of quiesce at this point

        //set resume signal to resume the cores that are quiesced
        //Note: we do not need a spinlock for this since we are in any
        //case the only core active until this point
        g_vmx_quiesce_resume_counter=0;
        //printf("\nCPU(0x%02x): waiting for other CPUs to resume...", vcpu->id);
        g_vmx_quiesce_resume_signal=1;

        while(g_vmx_quiesce_resume_counter < (g_midtable_numentries-1) );

        vcpu->quiesced=0;

        //printf("\nCPU(0x%02x): all CPUs resumed successfully.", vcpu->id);

        //reset resume signal
        spin_lock(&g_vmx_lock_quiesce_resume_signal);
        g_vmx_quiesce_resume_signal=0;
        spin_unlock(&g_vmx_lock_quiesce_resume_signal);

        // Reset flush all TLB signal
        if(g_vmx_flush_all_tlb_signal)
          g_vmx_flush_all_tlb_signal = 0;

        //release quiesce lock
        //printf("\nCPU(0x%02x): releasing quiesce lock.", vcpu->id);
        spin_unlock(&g_vmx_lock_quiesce);

}

//quiescing handler for #NMI (non-maskable interrupt) exception event
//note: we are in atomic processsing mode for this "vcpu"
// from_guest: 1 if NMI originated from the HVM (i.e. caller is intercept handler),
// otherwise 0 (within the hypervisor, i.e. caller is exception handler)
void xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception(VCPU *vcpu, struct regs *r, u32 from_guest){
	(void)r;

	/*
	 * If g_vmx_quiesce = 1, process quiesce regardless of where NMI originated
	 * from.
	 *
	 * If vcpu->quiesced = 1 (i.e. this core has been quiesced), simply return.
	 * This can only happen for the CPU calling
	 * xmhf_smpguest_arch_x86vmx_quiesce(). For other CPUs, NMIs are
	 * blocked during the time where vcpu->quiesced = 1.
	 */
  /*
   * Issue 1: If two cores request CPU quiescing at the same time, will an NMI be incorrectly injected to guest?
   * Issue 2: Will it be simpler to use an exception (e.g., one reserved exception in 22-27, see https://wiki.osdev.org/Exceptions)
   * instead of NMI?
   * Issue 3: The function always inject NMI to the *current* guest, not the *correct* guest. Will it cause problem? For
   * example, NMIs may be injected to PALs, not the red OS.
   * Issue 4: If we decide (1) not using NMI for CPU quiescing, and (2) the function always inject NMI to the current guest
   * for simplicity, then TrustVisor must be modified to inject NMI to the red OS.
   * Issue 5: Will the "__control_VMX_cpu_based" code in <xmhf_smpguest_arch_x86vmx_eventhandler_nmiexception> and
   * virtual NMI VMExit mismatch when there are multiple guests/domains? In other words, they are reading/writing different VMCS.
   */

  // The function handles NMI as follows:
  // (1) If XMHF on core i requests quiesce and the current core is not quiesced yet, XMHF must quiesce the current core
  // (2) If XMHF on core i requests quiesce and the current core is quiesced, then some device must issue NMI after core i
  // requesting quiesce. This NMI should be injected to a guest. XMHF currently injects NMI to the trapped guest.
  //      - [TODO] XMHF should query hypapp to find out which guest should receive this NMI
  // (3) If no one requests quiesce and the current core receives NMI, then it should be injected to the trapped guest.
	if(g_vmx_quiesce && !vcpu->quiesced){
		vcpu->quiesced=1;

		//increment quiesce counter
		spin_lock(&g_vmx_lock_quiesce_counter);
		g_vmx_quiesce_counter++;
		spin_unlock(&g_vmx_lock_quiesce_counter);

		//wait until quiesceing is finished
		//printf("\nCPU(0x%02x): Quiesced", vcpu->id);
		while(!g_vmx_quiesce_resume_signal);
		//printf("\nCPU(0x%02x): EOQ received, resuming...", vcpu->id);

    // Flush EPT TLB, if instructed so
    if(g_vmx_flush_all_tlb_signal)
      xmhf_memprot_flushmappings_localtlb(vcpu);

		spin_lock(&g_vmx_lock_quiesce_resume_counter);
		g_vmx_quiesce_resume_counter++;
		spin_unlock(&g_vmx_lock_quiesce_resume_counter);

		vcpu->quiesced=0;
	}else{
		//we are not in quiesce, inject the NMI to guest

		/*
		 * We want to set vcpu->vmcs.control_VMX_cpu_based, but we may be in an
		 * exception handler that is interrupting an intercept handler using
		 * vcpu->vmcs.control_VMX_cpu_based. This can cause race conditions.
		 *
		 * We know that this function only wants to set the 22nd bit of
		 * vcpu->vmcs.control_VMX_cpu_based.
		 *
		 * We observe that the intercept handlers are always having the
		 * following logic:
		 * 1. VMREAD reg
		 * 2. vcpu->vmcs.control_VMX_cpu_based = reg
		 * 3. update vcpu->vmcs.control_VMX_cpu_based
		 * 4. reg = vcpu->vmcs.control_VMX_cpu_based
		 * 5. VMWRITE reg
		 *
		 * Step 1 and 2 are in xmhf_baseplatform_arch_x86vmx_getVMCS(). Step
		 * 3 is body of the intercept handler. Step 4 and 5 are in
		 * xmhf_baseplatform_arch_x86vmx_putVMCS().
		 *
		 * To solve the problem, this function also sets
		 * vcpu->vmx_guest_inject_nmi. After step 5,
		 * xmhf_baseplatform_arch_x86vmx_putVMCS() checks whether
		 * vcpu->vmx_guest_inject_nmi is set. If so, it will perform another
		 * VMWRITE.
		 *
		 * So the updated logic of intercept handlers become
		 * 1. vcpu->vmx_guest_inject_nmi = 0
		 * 2. VMREAD reg
		 * 3. vcpu->vmcs.control_VMX_cpu_based = reg
		 * 4. Update vcpu->vmcs.control_VMX_cpu_based
		 * 5. reg = vcpu->vmcs.control_VMX_cpu_based
		 * 6. VMWRITE reg
		 * 7. if (vcpu->vmx_guest_inject_nmi) {
		 * 8.     VMREAD reg
		 * 9.     set bit 22 of reg
		 * 10.    VMWRITE reg
		 * 11.}
		 *
		 * The logic of this function is (appears atomic)
		 * 1. VMREAD reg
		 * 2. set bit 22 of reg
		 * 3. VMWRITE reg
		 * 4. vcpu->vmx_guest_inject_nmi = 1
		 *
		 * Consider different places this function interleaves with the
		 * intercept handler:
		 * a. before step 2: VMREAD at step 2 gets updated value, good
		 * b. between 2 - 6: VMREAD at step 2 gets old value, this function
		 *    writes new value, then overwritten by VMWRITE at step 6. But the
		 *    vmx_guest_inject_nmi flag bit will cause the intercept handler to
		 *    set the bit in VMCS correctly.
		 * c. between 6 - 7: this function will read the new value, good.
		 *    then step 7 will set bit 22 again, but it does not affect
		 *    correctness.
		 * d. after step 7: the bit 22 will finally be set, and the change to
		 *    the VMCS field made by the intercept handle is always preserved.
		 */
		//printf("\nCPU(0x%02x): Regular NMI, injecting back to guest...", vcpu->id);
		// TODO: if hypapp has multiple VMCS, need to select which one to inject
		/* Cannot be u32 in amd64, because VMREAD writes 64-bits */
		unsigned long __control_VMX_cpu_based;
		HALT_ON_ERRORCOND(__vmx_vmread(0x4002, &__control_VMX_cpu_based));
		__control_VMX_cpu_based |= (1U << 22);
		HALT_ON_ERRORCOND(__vmx_vmwrite(0x4002, __control_VMX_cpu_based));
		vcpu->vmx_guest_inject_nmi = 1;
	}

	/* Unblock NMI in hypervisor */
	if (from_guest) {
		xmhf_smpguest_arch_x86vmx_unblock_nmi();
	}
}

//----------------------------------------------------------------------


//perform required setup after a guest awakens a new CPU
void xmhf_smpguest_arch_x86vmx_postCPUwakeup(VCPU *vcpu){
	//setup guest CS and EIP as specified by the SIPI vector
	vcpu->vmcs.guest_CS_selector = ((vcpu->sipivector * PAGE_SIZE_4K) >> 4);
	vcpu->vmcs.guest_CS_base = (vcpu->sipivector * PAGE_SIZE_4K);
	vcpu->vmcs.guest_RIP = 0x0ULL;
}

//walk guest page tables; returns pointer to corresponding guest physical address
//note: returns 0xFFFFFFFF if there is no mapping
u8 * xmhf_smpguest_arch_x86vmx_walk_pagetables(VCPU *vcpu, u32 vaddr){
  if((u32)vcpu->vmcs.guest_CR4 & CR4_PAE ){
    //PAE paging used by guest
    u32 kcr3 = (u32)vcpu->vmcs.guest_CR3;
    u32 pdpt_index, pd_index, pt_index, offset;
    u64 paddr;
    pdpt_t kpdpt;
    pdt_t kpd;
    pt_t kpt;
    u32 pdpt_entry, pd_entry, pt_entry;
    uintptr_t tmp;

    // get fields from virtual addr
    pdpt_index = pae_get_pdpt_index(vaddr);
    pd_index = pae_get_pdt_index(vaddr);
    pt_index = pae_get_pt_index(vaddr);
    offset = pae_get_offset_4K_page(vaddr);

    //grab pdpt entry
    tmp = pae_get_addr_from_32bit_cr3(kcr3);
    kpdpt = (pdpt_t)((uintptr_t)tmp);
    pdpt_entry = kpdpt[pdpt_index];

    //grab pd entry
    tmp = pae_get_addr_from_pdpe(pdpt_entry);
    kpd = (pdt_t)((uintptr_t)tmp);
    pd_entry = kpd[pd_index];

    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (uintptr_t)pae_get_addr_from_pde(pd_entry);
      kpt = (pt_t)((uintptr_t)tmp);
      pt_entry  = kpt[pt_index];

      // find physical page base addr from page table entry
      paddr = (u64)pae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 2MB page
      offset = pae_get_offset_big(vaddr);
      paddr = (u64)pae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }

    return (u8 *)(uintptr_t)paddr;

  }else{
    //non-PAE 2 level paging used by guest
    u32 kcr3 = (u32)vcpu->vmcs.guest_CR3;
    u32 pd_index, pt_index, offset;
    u64 paddr;
    npdt_t kpd;
    npt_t kpt;
    u32 pd_entry, pt_entry;
    uintptr_t tmp;

    // get fields from virtual addr
    pd_index = npae_get_pdt_index(vaddr);
    pt_index = npae_get_pt_index(vaddr);
    offset = npae_get_offset_4K_page(vaddr);

    // grab pd entry
    tmp = npae_get_addr_from_32bit_cr3(kcr3);
    kpd = (npdt_t)((uintptr_t)tmp);
    pd_entry = kpd[pd_index];

    if ( (pd_entry & _PAGE_PSE) == 0 ) {
      // grab pt entry
      tmp = (uintptr_t)npae_get_addr_from_pde(pd_entry);
      kpt = (npt_t)((uintptr_t)tmp);
      pt_entry  = kpt[pt_index];

      // find physical page base addr from page table entry
      paddr = (u64)npae_get_addr_from_pte(pt_entry) + offset;
    }
    else { // 4MB page
      offset = npae_get_offset_big(vaddr);
      paddr = (u64)npae_get_addr_from_pde_big(pd_entry);
      paddr += (u64)offset;
    }

    return (u8 *)(uintptr_t)paddr;
  }
}
