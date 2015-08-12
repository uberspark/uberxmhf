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
 * x86 cpu hardware model implementation
 * author: amit vasudevan (amitvasudevan@acm.org)
*/


#include <xmhf.h>
#include <xmhf-hwm.h>

u32 xmhfhwm_cpu_gprs_eip = 0;
u32 xmhfhwm_cpu_gprs_esp = 0;

u32 xmhfhwm_cpu_gprs_eax = 0;
u32 xmhfhwm_cpu_gprs_ebx = 0;
u32 xmhfhwm_cpu_gprs_edx = 0;
u32 xmhfhwm_cpu_gprs_ecx = 0;
u32 xmhfhwm_cpu_gprs_esi = 0;
u32 xmhfhwm_cpu_gprs_edi = 0;

u32 xmhfhwm_cpu_eflags = 0;

u16 xmhfhwm_cpu_gdtr_limit=0;
u32 xmhfhwm_cpu_gdtr_base=0;
u16 xmhfhwm_cpu_idtr_limit=0;
u32 xmhfhwm_cpu_idtr_base=0;

void _impl_xmhfhwm_cpu_insn_hlt(void){
	//@assert 0;
	while(1);
}



void _impl_xmhfhwm_cpu_insn_pushl_mesp(int index){
	u32 value;
	value = *((u32 *)(xmhfhwm_cpu_gprs_esp + index));
	xmhfhwm_cpu_gprs_esp -= sizeof(u32);
	*((u32 *)xmhfhwm_cpu_gprs_esp) = value;
}

void _impl_xmhfhwm_cpu_insn_pushl_mem(u32 value){
	xmhfhwm_cpu_gprs_esp -= sizeof(u32);
	*((u32 *)xmhfhwm_cpu_gprs_esp) = value;
}


u32 _impl_xmhfhwm_cpu_insn_popl_mem(void){
	u32 value = *((u32 *)xmhfhwm_cpu_gprs_esp);
	xmhfhwm_cpu_gprs_esp += sizeof(u32);
	return value;
}

void _impl_xmhfhwm_cpu_insn_addl_imm_esp(u32 value){
	xmhfhwm_cpu_gprs_esp += value;
}


void _impl_xmhfhwm_cpu_insn_movl_mesp_eax(int index){
	u32 *value;
	value = (u32 *)((u32)((int)xmhfhwm_cpu_gprs_esp + (int)index));
	xmhfhwm_cpu_gprs_eax = *value;
}

void _impl_xmhfhwm_cpu_insn_movl_mesp_ecx(int index){
	u32 *value;
	value = (u32 *)((u32)((int)xmhfhwm_cpu_gprs_esp + (int)index));
	xmhfhwm_cpu_gprs_ecx = *value;
}

void _impl_xmhfhwm_cpu_insn_cmpl_imm_meax(u32 value, int index){
	uint32_t value_meax;
	value_meax = *((uint32_t *)((uint32_t)((int32_t)xmhfhwm_cpu_gprs_eax + (int32_t)index)));

	//XXX: TODO propagation of CF, PF, AF, SF and OF
        if(value_meax - value == 0)
		xmhfhwm_cpu_eflags |= EFLAGS_ZF;

}


void _impl_xmhfhwm_cpu_insn_movl_imm_meax(u32 value, int index){
	uint32_t *value_meax;
	value_meax = (uint32_t *)((uint32_t)((int32_t)xmhfhwm_cpu_gprs_eax + (int32_t)index));
	*value_meax = value;
}

void _impl_xmhfhwm_cpu_insn_movl_meax_edx(int index){
	uint32_t value_meax;
	value_meax = *((uint32_t *)((uint32_t)((int32_t)xmhfhwm_cpu_gprs_eax + (int32_t)index)));
	xmhfhwm_cpu_gprs_edx = value_meax;
}

void _impl_xmhfhwm_cpu_insn_movl_meax_ecx(int index){
	uint32_t value_meax;
	value_meax = *((uint32_t *)((uint32_t)((int32_t)xmhfhwm_cpu_gprs_eax + (int32_t)index)));
	xmhfhwm_cpu_gprs_ecx = value_meax;
}

void _impl_xmhfhwm_cpu_insn_movl_ecx_meax(int index){
	uint32_t *value_meax;
	value_meax = (uint32_t *)((uint32_t)((int32_t)xmhfhwm_cpu_gprs_eax + (int32_t)index));
	*value_meax = xmhfhwm_cpu_gprs_ecx;
}


void _impl_xmhfhwm_cpu_insn_movl_edx_meax(int index){
	uint32_t *value_meax;
	value_meax = (uint32_t *)((uint32_t)((int32_t)xmhfhwm_cpu_gprs_eax + (int32_t)index));
	*value_meax = xmhfhwm_cpu_gprs_edx;
}

void _impl_xmhfhwm_cpu_insn_bsrl_mesp_eax(int index){
	uint32_t value = *((uint32_t *)((uint32_t)((int32_t)xmhfhwm_cpu_gprs_esp + (int32_t)index)));
	u32 i;
	for(i=31; i >=0; i--){
		if(value & (1UL << i)){
			xmhfhwm_cpu_gprs_eax = i;
			return;
		}
	}
}

void _impl_xmhfhwm_cpu_insn_pushl_esi(void){
	xmhfhwm_cpu_gprs_esp -= sizeof(u32);
	*((u32 *)xmhfhwm_cpu_gprs_esp) = xmhfhwm_cpu_gprs_esi;
}

void _impl_xmhfhwm_cpu_insn_pushl_ebx(void){
	xmhfhwm_cpu_gprs_esp -= sizeof(u32);
	*((u32 *)xmhfhwm_cpu_gprs_esp) = xmhfhwm_cpu_gprs_ebx;
}

void _impl_xmhfhwm_cpu_insn_movl_mecx_ecx(int index){
	uint32_t value_mecx;
	value_mecx = *((uint32_t *)((uint32_t)((int32_t)xmhfhwm_cpu_gprs_ecx + (int32_t)index)));
	xmhfhwm_cpu_gprs_ecx = value_mecx;
}


void _impl_xmhfhwm_cpu_insn_cpuid(void){
	//XXX: TODO
	xmhfhwm_cpu_gprs_ebx = 0;
	xmhfhwm_cpu_gprs_edx = 0;
}

void _impl_xmhfhwm_cpu_insn_movl_mesp_esi(int index){
	u32 *value;
	value = (u32 *)((u32)((int)xmhfhwm_cpu_gprs_esp + (int)index));
	xmhfhwm_cpu_gprs_esi = *value;
}

void _impl_xmhfhwm_cpu_insn_movl_eax_mesi(int index){
	u32 *value;
	value = (u32 *)((u32)((int)xmhfhwm_cpu_gprs_esi + (int)index));
	*value = xmhfhwm_cpu_gprs_eax;
}

void _impl_xmhfhwm_cpu_insn_movl_ebx_mesi(int index){
	u32 *value;
	value = (u32 *)((u32)((int)xmhfhwm_cpu_gprs_esi + (int)index));
	*value = xmhfhwm_cpu_gprs_ebx;
}

void _impl_xmhfhwm_cpu_insn_movl_ecx_mesi(int index){
	u32 *value;
	value = (u32 *)((u32)((int)xmhfhwm_cpu_gprs_esi + (int)index));
	*value = xmhfhwm_cpu_gprs_ecx;
}

void _impl_xmhfhwm_cpu_insn_movl_edx_mesi(int index){
	u32 *value;
	value = (u32 *)((u32)((int)xmhfhwm_cpu_gprs_esi + (int)index));
	*value = xmhfhwm_cpu_gprs_edx;
}

void _impl_xmhfhwm_cpu_insn_popl_eax(void){
	u32 value = *((u32 *)xmhfhwm_cpu_gprs_esp);
	xmhfhwm_cpu_gprs_esp += sizeof(u32);
	xmhfhwm_cpu_gprs_eax = value;
}

void _impl_xmhfhwm_cpu_insn_popl_esi(void){
	u32 value = *((u32 *)xmhfhwm_cpu_gprs_esp);
	xmhfhwm_cpu_gprs_esp += sizeof(u32);
	xmhfhwm_cpu_gprs_esi = value;
}

void _impl_xmhfhwm_cpu_insn_popl_ebx(void){
	u32 value = *((u32 *)xmhfhwm_cpu_gprs_esp);
	xmhfhwm_cpu_gprs_esp += sizeof(u32);
	xmhfhwm_cpu_gprs_ebx = value;
}

void _impl_xmhfhwm_cpu_insn_cli(void){
	xmhfhwm_cpu_eflags &= ~(EFLAGS_IF);
}

void _impl_xmhfhwm_cpu_insn_sti(void){
	xmhfhwm_cpu_eflags |= (EFLAGS_IF);
}

void _impl_xmhfhwm_cpu_insn_subl_imm_esp(u32 value){
	xmhfhwm_cpu_gprs_esp -= value;
}

void _impl_xmhfhwm_cpu_insn_sgdt_mesp(int index){
	u32 *tmem_gdtbase;
	u16 *tmem_gdtlimit;
	tmem_gdtlimit = (u16 *)((u32)((int)xmhfhwm_cpu_gprs_esp + (int)index));
	tmem_gdtbase = (u32 *)((u32)((int)xmhfhwm_cpu_gprs_esp + (int)index) + sizeof(u32));
	*tmem_gdtlimit = xmhfhwm_cpu_gdtr_limit;
	*tmem_gdtbase = xmhfhwm_cpu_gdtr_base;
}

void _impl_xmhfhwm_cpu_insn_xorl_edx_edx(void){
	xmhfhwm_cpu_gprs_edx = 0;
}

void _impl_xmhfhwm_cpu_insn_sidt_mesp(int index){
	u32 *tmem_idtbase;
	u16 *tmem_idtlimit;
	tmem_idtlimit = (u16 *)((u32)((int)xmhfhwm_cpu_gprs_esp + (int)index));
	tmem_idtbase = (u32 *)((u32)((int)xmhfhwm_cpu_gprs_esp + (int)index) + sizeof(u32));
	*tmem_idtlimit = xmhfhwm_cpu_idtr_limit;
	*tmem_idtbase = xmhfhwm_cpu_idtr_base;
}
