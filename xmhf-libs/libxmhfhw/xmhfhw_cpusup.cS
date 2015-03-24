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

//xmhfhw_cpu - base CPU functions
//author: amit vasudevan (amitvasudevan@acm.org)

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfhw.h>
#include <xmhf-debug.h>


__attribute__((naked)) void cpu_relax(void){
    xmhfhwm_cpu_insn_pause();
    xmhfhwm_cpu_insn_ret();
}


__attribute__((naked)) void xmhfhw_cpu_cpuid(u32 op,    //0xC
                                             u32 *eax,  //0x10
                                             u32 *ebx,  //0x14
                                             u32 *ecx,  //0x18
                                             u32 *edx){ //0x1C

    xmhfhwm_cpu_insn_pushl_esi();
    xmhfhwm_cpu_insn_pushl_ebx();

    xmhfhwm_cpu_insn_movl_mesp_eax(0xc); //eax = op
    xmhfhwm_cpu_insn_movl_mesp_ecx(0x18);
    xmhfhwm_cpu_insn_movl_mecx_ecx(0x0);

    xmhfhwm_cpu_insn_cpuid();

    xmhfhwm_cpu_insn_movl_mesp_esi(0x10);
    xmhfhwm_cpu_insn_movl_eax_mesi(0x0);
    xmhfhwm_cpu_insn_movl_mesp_esi(0x14);
    xmhfhwm_cpu_insn_movl_ebx_mesi(0x0);
    xmhfhwm_cpu_insn_movl_mesp_esi(0x18);
    xmhfhwm_cpu_insn_movl_ecx_mesi(0x0);
    xmhfhwm_cpu_insn_movl_mesp_esi(0x1c);
    xmhfhwm_cpu_insn_movl_edx_mesi(0x0);

    xmhfhwm_cpu_insn_popl_eax();
    xmhfhwm_cpu_insn_popl_esi();
    xmhfhwm_cpu_insn_ret();
}




__attribute__((naked)) uint64_t rdtsc64(void){
    xmhfhwm_cpu_insn_rdtsc();
    xmhfhwm_cpu_insn_ret();
}


__attribute__((naked)) u32 read_eflags(void){
    xmhfhwm_cpu_insn_pushfl();
    xmhfhwm_cpu_insn_popl_eax();
    xmhfhwm_cpu_insn_ret();
}


__attribute__((naked)) void write_eflags(u32 eflags){
    xmhfhwm_cpu_insn_pushl_mesp(0x4);
    xmhfhwm_cpu_insn_popfl();
    xmhfhwm_cpu_insn_ret();
}





/* Calls to read and write control registers */
__attribute__((naked)) u64 read_cr0(void){
    xmhfhwm_cpu_insn_xorl_edx_edx();
    xmhfhwm_cpu_insn_movl_cr0_eax();
    xmhfhwm_cpu_insn_ret();
}


__attribute__((naked)) void write_cr0(u64 val){
  xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
  xmhfhwm_cpu_insn_movl_eax_cr0();
  xmhfhwm_cpu_insn_ret();
}

__attribute__((naked)) u32 read_cr2(void){
  xmhfhwm_cpu_insn_movl_cr2_eax();
  xmhfhwm_cpu_insn_ret();
}

__attribute__((naked)) u64 read_cr3(void){
    xmhfhwm_cpu_insn_xorl_edx_edx();
    xmhfhwm_cpu_insn_movl_cr3_eax();
    xmhfhwm_cpu_insn_ret();
}

__attribute__((naked)) u64 read_rsp(void){
    xmhfhwm_cpu_insn_xorl_edx_edx();
    xmhfhwm_cpu_insn_movl_esp_eax();
    xmhfhwm_cpu_insn_ret();
}

__attribute__((naked)) u32 read_esp(void){
    xmhfhwm_cpu_insn_movl_esp_eax();
    xmhfhwm_cpu_insn_ret();
}


__attribute__((naked)) void write_cr3(u64 val){
  xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
  xmhfhwm_cpu_insn_movl_eax_cr3();
  xmhfhwm_cpu_insn_ret();
}


__attribute__((naked)) u64 read_cr4(void){
    xmhfhwm_cpu_insn_xorl_edx_edx();
    xmhfhwm_cpu_insn_movl_cr4_eax();
    xmhfhwm_cpu_insn_ret();
}

__attribute__((naked)) void write_cr4(u64 val){
  xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
  xmhfhwm_cpu_insn_movl_eax_cr4();
  xmhfhwm_cpu_insn_ret();
}



/*void skinit(unsigned long eax) {
    __asm__("mov %0, %%eax": :"r" (eax));
    __asm__("skinit %%eax":);
}*/


//segment register access
__attribute__((naked)) u32 read_segreg_cs(void){
  xmhfhwm_cpu_insn_movl_cs_eax();
  xmhfhwm_cpu_insn_ret();
}

__attribute__((naked)) u32 read_segreg_ds(void){
  xmhfhwm_cpu_insn_movl_ds_eax();
  xmhfhwm_cpu_insn_ret();
}

__attribute__((naked)) u32 read_segreg_es(void){
  xmhfhwm_cpu_insn_movl_es_eax();
  xmhfhwm_cpu_insn_ret();
}

__attribute__((naked)) u32 read_segreg_fs(void){
  xmhfhwm_cpu_insn_movl_fs_eax();
  xmhfhwm_cpu_insn_ret();
}

__attribute__((naked)) u32 read_segreg_gs(void){
  xmhfhwm_cpu_insn_movl_gs_eax();
  xmhfhwm_cpu_insn_ret();

}

__attribute__((naked)) u32 read_segreg_ss(void){
  xmhfhwm_cpu_insn_movl_ss_eax();
  xmhfhwm_cpu_insn_ret();
}








__attribute__((naked)) u16 read_tr_sel(void){
  xmhfhwm_cpu_insn_xorl_eax_eax();
  xmhfhwm_cpu_insn_str_ax();
  xmhfhwm_cpu_insn_ret();
}



__attribute__((naked)) void wbinvd(void)
{
    xmhfhwm_cpu_insn_wbinvd();
    xmhfhwm_cpu_insn_ret();
}





__attribute__((naked)) uint32_t bsrl(uint32_t mask)
{
    xmhfhwm_cpu_insn_bsrl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_ret();
}





__attribute__((naked)) void xmhfhw_cpu_disable_intr(void){
    xmhfhwm_cpu_insn_cli();
    xmhfhwm_cpu_insn_ret();
}

__attribute__((naked)) void enable_intr(void)
{
    xmhfhwm_cpu_insn_sti();
    xmhfhwm_cpu_insn_ret();
}


//////
//get extended control register (xcr)
__attribute__((naked)) u64 xgetbv(u32 xcr_reg){
    xmhfhwm_cpu_insn_movl_mesp_ecx(0x4);
    xmhfhwm_cpu_insn_xgetbv();
    xmhfhwm_cpu_insn_ret();
}

//////
//set extended control register (xcr)
void xsetbv(u32 xcr_reg, u64 value){
    xmhfhwm_cpu_insn_movl_mesp_ecx(0x4);
    xmhfhwm_cpu_insn_movl_mesp_eax(0x8);
    xmhfhwm_cpu_insn_movl_mesp_edx(0xC);
    xmhfhwm_cpu_insn_xsetbv();
    xmhfhwm_cpu_insn_ret();
}



/*
void sysexitq(u64 rip, u64 rsp){


    //TODO: x86_64 --> x86
            asm volatile(
                 "movq %0, %%rdx \r\n"
                 "movq %1, %%rcx \r\n"

                 "sysexitq \r\n"
                 //"int $0x03 \r\n"
                 //"1: jmp 1b \r\n"
                :
                : "m" (rip),
                  "m" (rsp)
                : "rdx", "rcx"
            );


}*/




//////
__attribute__((naked)) void spin_lock(volatile u32 *lock){
    xmhfhwm_cpu_insn_movl_mesp_ecx(0x4);
    CASM_LABEL(splock);
    xmhfhwm_cpu_insn_btl_imm_mecx(0x0, 0x0);
    xmhfhwm_cpu_insn_jnc(splock);
    xmhfhwm_cpu_insn_lock();
    xmhfhwm_cpu_insn_btrl_imm_mecx(0x0,0x0);
    xmhfhwm_cpu_insn_jnc(splock);
    xmhfhwm_cpu_insn_ret();

}


//////
__attribute__((naked)) void spin_unlock(volatile u32 *lock){
    xmhfhwm_cpu_insn_movl_mesp_ecx(0x4);
    xmhfhwm_cpu_insn_btsl_imm_mecx(0x0,0x0);
    xmhfhwm_cpu_insn_ret();
}



//////
//load CPU GDT
__attribute__((naked)) void xmhfhw_cpu_loadGDT(arch_x86_gdtdesc_t *gdt_addr){
    xmhfhwm_cpu_insn_movl_mesp_ecx(0x4);
    xmhfhwm_cpu_insn_lgdt_mecx(0x0);
    xmhfhwm_cpu_insn_ret();
}



//////
//load CPU TR
__attribute__((naked)) void xmhfhw_cpu_loadTR(u32 tr_selector){
    xmhfhwm_cpu_insn_movl_mesp_eax(0x4);
    xmhfhwm_cpu_insn_ltr_ax();
    xmhfhwm_cpu_insn_ret();
}



//////
//load CPU IDT
__attribute__((naked)) void xmhfhw_cpu_loadIDT(arch_x86_idtdesc_t *idt_addr){
    xmhfhwm_cpu_insn_movl_mesp_ecx(0x4);
    xmhfhwm_cpu_insn_lidt_mecx(0x0);
    xmhfhwm_cpu_insn_ret();
}



//////
__attribute__((naked)) u64 xmhf_baseplatform_arch_x86_getgdtbase(void){
		xmhfhwm_cpu_insn_subl_imm_esp(0x8);
		xmhfhwm_cpu_insn_sgdt_mesp(0x0);
		xmhfhwm_cpu_insn_movl_mesp_eax(0x2);
		xmhfhwm_cpu_insn_xorl_edx_edx();
        xmhfhwm_cpu_insn_addl_imm_esp(0x8);
        xmhfhwm_cpu_insn_ret();
}





//////
__attribute__((naked)) u64 xmhf_baseplatform_arch_x86_getidtbase(void){
		xmhfhwm_cpu_insn_subl_imm_esp(0x8);
		xmhfhwm_cpu_insn_sidt_mesp(0x0);
		xmhfhwm_cpu_insn_movl_mesp_eax(0x2);
		xmhfhwm_cpu_insn_xorl_edx_edx();
        xmhfhwm_cpu_insn_addl_imm_esp(0x8);
        xmhfhwm_cpu_insn_ret();
}




//////
__attribute__((naked)) u64  xmhf_baseplatform_arch_x86_gettssbase(void){
    xmhfhwm_cpu_insn_subl_imm_esp(0x8);
    xmhfhwm_cpu_insn_sgdt_mesp(0x0);
    xmhfhwm_cpu_insn_movl_mesp_ecx(0x2);
    xmhfhwm_cpu_insn_xorl_eax_eax();
    xmhfhwm_cpu_insn_str_ax();
    xmhfhwm_cpu_insn_addl_eax_ecx();		//%ecx is pointer to TSS descriptor in GDT
    xmhfhwm_cpu_insn_movl_mecx_eax(0x0);	//eax = low 32-bits of TSS descriptor
    xmhfhwm_cpu_insn_addl_imm_ecx(0x4);		//%ecx points to top 32-bits of 64-bit TSS desc.
    xmhfhwm_cpu_insn_movl_mecx_edx(0x0);	//edx = high 32-bits of TSS descriptor

    xmhfhwm_cpu_insn_movl_edx_ecx();
    xmhfhwm_cpu_insn_andl_imm_edx(0xFF000000);
    xmhfhwm_cpu_insn_andl_imm_ecx(0x000000FF);
    xmhfhwm_cpu_insn_shl_imm_ecx(16);
    xmhfhwm_cpu_insn_shr_imm_eax(16);
    xmhfhwm_cpu_insn_orl_ecx_eax();
    xmhfhwm_cpu_insn_orl_edx_eax();
    xmhfhwm_cpu_insn_xorl_edx_edx();

    xmhfhwm_cpu_insn_addl_imm_esp(0x8);
    xmhfhwm_cpu_insn_ret();
}

















