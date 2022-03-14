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

/*
 * EMHF exception handler component interface
 * x86 arch. backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>

//---function to obtain the vcpu of the currently executing core----------------
// XXX: TODO, move this into baseplatform as backend
// note: this always returns a valid VCPU pointer
static VCPU *_svm_and_vmx_getvcpu(void){
  int i;
  u32 eax, edx, *lapic_reg;
  u32 lapic_id;

  //read LAPIC id of this core
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G
  eax &= (u32)0xFFFFF000UL;
  lapic_reg = (u32 *)((uintptr_t)eax + (uintptr_t)LAPIC_ID);
  lapic_id = *lapic_reg;
  //printf("\n%s: lapic base=0x%08x, id reg=0x%08x", __FUNCTION__, eax, lapic_id);
  lapic_id = lapic_id >> 24;
  //printf("\n%s: lapic_id of core=0x%02x", __FUNCTION__, lapic_id);

  for(i=0; i < (int)g_midtable_numentries; i++){
    if(g_midtable[i].cpu_lapic_id == lapic_id)
        return( (VCPU *)g_midtable[i].vcpu_vaddr_ptr );
  }

  printf("\n%s: fatal, unable to retrieve vcpu for id=0x%02x", __FUNCTION__, lapic_id);
  HALT(); return NULL; // will never return presently
}

//initialize EMHF core exception handlers
void xmhf_xcphandler_arch_initialize(void){
    uintptr_t *pexceptionstubs;
    uintptr_t i;

    printf("\n%s: setting up runtime IDT...", __FUNCTION__);

    pexceptionstubs = (uintptr_t *)&xmhf_xcphandler_exceptionstubs;

    for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
#ifdef __X86_64__
        idtentry_t *idtentry=(idtentry_t *)((hva_t)xmhf_xcphandler_arch_get_idt_start()+ (i*16));
        idtentry->isrLow16 = (u16)(pexceptionstubs[i]);
        idtentry->isrHigh16 = (u16)(pexceptionstubs[i] >> 16);
        idtentry->isrHigh32 = (u32)(pexceptionstubs[i] >> 32);
        idtentry->isrSelector = __CS;
        idtentry->count = 0x0;  // for now, set IST to 0
        idtentry->type = 0x8E;  // 64-bit interrupt gate
                                // present=1, DPL=00b, system=0, type=1110b
        idtentry->reserved_zero = 0x0;
#else /* !__X86_64__ */
        idtentry_t *idtentry=(idtentry_t *)((hva_t)xmhf_xcphandler_arch_get_idt_start()+ (i*8));
        idtentry->isrLow= (u16)pexceptionstubs[i];
        idtentry->isrHigh= (u16) ( (u32)pexceptionstubs[i] >> 16 );
        idtentry->isrSelector = __CS;
        idtentry->count=0x0;
        idtentry->type=0x8E;    //32-bit interrupt gate
                                //present=1, DPL=00b, system=0, type=1110b
#endif /* __X86_64__ */
    }

    printf("\n%s: IDT setup done.", __FUNCTION__);
}


//get IDT start address
u8 * xmhf_xcphandler_arch_get_idt_start(void){
    return (u8 *)&xmhf_xcphandler_idt_start;
}

extern uint8_t _begin_xcph_table[];
extern uint8_t _end_xcph_table[];

//EMHF exception handler hub
void xmhf_xcphandler_arch_hub(uintptr_t vector, struct regs *r){
    VCPU *vcpu;

    vcpu = _svm_and_vmx_getvcpu();

    /*
     * Cannot print anything before event handler returns if this exception
     * is for quiescing (vector == CPU_EXCEPTION_NMI), otherwise will deadlock.
     * See xmhf_smpguest_arch_x86vmx_quiesce().
     */

    switch(vector){
    case CPU_EXCEPTION_NMI:
        xmhf_smpguest_arch_x86_eventhandler_nmiexception(vcpu, r, 0);
        break;

    default:
        {
            /*
             * Search for matching exception in .xcph_table section.
             * Each entry in .xcph_table has 3 long values. If the first value
             * matches the exception vector and the second value matches the
             * current PC, then jump to the third value.
             *
             * In x86, these names should be interpreted as EIP and EFLAGS, not
             * RIP and RFLAGS.
             */
            uintptr_t exception_cs, exception_rip, exception_rflags;
            u32 error_code_available = 0;
            hva_t *found = NULL;

            // skip error code on stack if applicable
            if (vector == CPU_EXCEPTION_DF ||
                vector == CPU_EXCEPTION_TS ||
                vector == CPU_EXCEPTION_NP ||
                vector == CPU_EXCEPTION_SS ||
                vector == CPU_EXCEPTION_GP ||
                vector == CPU_EXCEPTION_PF ||
                vector == CPU_EXCEPTION_AC) {
                error_code_available = 1;
#ifdef __X86_64__
                r->rsp += sizeof(uintptr_t);
#else /* !__X86_64__ */
                r->esp += sizeof(uintptr_t);
#endif /* __X86_64__ */
            }

#ifdef __X86_64__
            exception_rip = ((uintptr_t *)(r->rsp))[0];
            exception_cs = ((uintptr_t *)(r->rsp))[1];
            exception_rflags = ((uintptr_t *)(r->rsp))[2];
#else /* !__X86_64__ */
            exception_rip = ((uintptr_t *)(r->esp))[0];
            exception_cs = ((uintptr_t *)(r->esp))[1];
            exception_rflags = ((uintptr_t *)(r->esp))[2];
#endif /* __X86_64__ */

            for (hva_t *i = (hva_t *)_begin_xcph_table;
                 i < (hva_t *)_end_xcph_table; i += 3) {
                if (i[0] == vector && i[1] == exception_rip) {
                    found = i;
                    break;
                }
            }

            if (found) {
                /* Found in xcph table; Modify EIP on stack and iret */
                printf("\nFound in xcph table");
#ifdef __X86_64__
                ((uintptr_t *)(r->rsp))[0] = found[2];
#else /* !__X86_64__ */
                ((uintptr_t *)(r->esp))[0] = found[2];
#endif /* __X86_64__ */
                break;
            }

            /* Print exception and halt */
            printf("\n[%02x]: unhandled exception %d (0x%x), halting!",
                    vcpu->id, vector, vector);
            if (error_code_available) {
#ifdef __X86_64__
                printf("\n[%02x]: error code: 0x%016lx", vcpu->id, ((uintptr_t *)(r->rsp))[-1]);
#else /* !__X86_64__ */
                printf("\n[%02x]: error code: 0x%08lx", vcpu->id, ((uintptr_t *)(r->esp))[-1]);
#endif /* __X86_64__ */
            }
            printf("\n[%02x]: state dump follows...", vcpu->id);
            // things to dump
#ifdef __X86_64__
            printf("\n[%02x] CS:RIP 0x%04x:0x%016lx with RFLAGS=0x%016lx", vcpu->id,
                (u16)exception_cs, exception_rip, exception_rflags);
            printf("\n[%02x]: VCPU at 0x%016lx", vcpu->id, (uintptr_t)vcpu, vcpu->id);
            printf("\n[%02x] RAX=0x%016lx RBX=0x%016lx", vcpu->id, r->rax, r->rbx);
            printf("\n[%02x] RCX=0x%016lx RDX=0x%016lx", vcpu->id, r->rcx, r->rdx);
            printf("\n[%02x] RSI=0x%016lx RDI=0x%016lx", vcpu->id, r->rsi, r->rdi);
            printf("\n[%02x] RBP=0x%016lx RSP=0x%016lx", vcpu->id, r->rbp, r->rsp);
            printf("\n[%02x] R8 =0x%016lx R9 =0x%016lx", vcpu->id, r->r8 , r->r9 );
            printf("\n[%02x] R10=0x%016lx R11=0x%016lx", vcpu->id, r->r10, r->r11);
            printf("\n[%02x] R12=0x%016lx R13=0x%016lx", vcpu->id, r->r12, r->r13);
            printf("\n[%02x] R14=0x%016lx R15=0x%016lx", vcpu->id, r->r14, r->r15);
#else /* !__X86_64__ */
            printf("\n[%02x] CS:EIP 0x%04x:0x%08x with EFLAGS=0x%08x", vcpu->id,
                (u16)exception_cs, exception_rip, exception_rflags);
            printf("\n[%02x]: VCPU at 0x%08x", vcpu->id, (u32)vcpu, vcpu->id);
            printf("\n[%02x] EAX=0x%08x EBX=0x%08x ECX=0x%08x EDX=0x%08x", vcpu->id,
                    r->eax, r->ebx, r->ecx, r->edx);
            printf("\n[%02x] ESI=0x%08x EDI=0x%08x EBP=0x%08x ESP=0x%08x", vcpu->id,
                    r->esi, r->edi, r->ebp, r->esp);
#endif /* __X86_64__ */
            printf("\n[%02x] CS=0x%04x, DS=0x%04x, ES=0x%04x, SS=0x%04x", vcpu->id,
                (u16)read_segreg_cs(), (u16)read_segreg_ds(),
                (u16)read_segreg_es(), (u16)read_segreg_ss());
            printf("\n[%02x] FS=0x%04x, GS=0x%04x", vcpu->id,
                (u16)read_segreg_fs(), (u16)read_segreg_gs());
            printf("\n[%02x] TR=0x%04x", vcpu->id, (u16)read_tr_sel());

            //do a stack dump in the hopes of getting more info.
            {
                //vcpu->rsp is the TOS
                uintptr_t i;
                printf("\n[%02x]-----stack dump-----", vcpu->id);
#ifdef __X86_64__
                for(i=r->rsp; i < vcpu->rsp; i+=sizeof(uintptr_t)){
                    printf("\n[%02x]  Stack(0x%016lx) -> 0x%016lx", vcpu->id, i, *(uintptr_t *)i);
                }
#else /* !__X86_64__ */
                for(i=r->esp; i < vcpu->esp; i+=sizeof(uintptr_t)){
                    printf("\n[%02x]  Stack(0x%08x) -> 0x%08x", vcpu->id, i, *(uintptr_t *)i);
                }
#endif /* __X86_64__ */
                printf("\n[%02x]-----end------------", vcpu->id);
            }

#ifdef __X86_64__
            // Exception #BP may be caused by failed VMRESUME. Dump VMCS
            // This function is not implemented in x86 yet
            if (vector == CPU_EXCEPTION_BP &&
                get_cpu_vendor_or_die() == CPU_VENDOR_INTEL) {
                xmhf_baseplatform_arch_x86vmx_getVMCS(vcpu);
                xmhf_baseplatform_arch_x86vmx_dump_vcpu(vcpu);
            }
#endif /* __X86_64__ */
            HALT();
        }
    }
}
