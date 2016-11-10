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
 * libxmhfhw CASM functions verification driver
 * author: amit vasudevan (amitvasudevan@acm.org)
*/


//#include <xmhf.h>
//#include <xmhf-hwm.h>
//#include <xmhfgeec.h>
//#include <xmhf-debug.h>
#include <uberspark.h>
#include <xmhfhw.h>

u32 cpuid = 0;	//BSP cpu

/*
//////
// frama-c non-determinism functions
//////

u32 Frama_C_entropy_source;

//@ assigns Frama_C_entropy_source \from Frama_C_entropy_source;
void Frama_C_update_entropy(void);

u32 framac_nondetu32(void){
  Frama_C_update_entropy();
  return (u32)Frama_C_entropy_source;
}

u32 framac_nondetu32interval(u32 min, u32 max)
{
  u32 r,aux;
  Frama_C_update_entropy();
  aux = Frama_C_entropy_source;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}
*/

//////
u32 saved_cpu_gprs_ebx=0;
u32 saved_cpu_gprs_esi=0;
u32 saved_cpu_gprs_edi=0;

void cabi_establish(void){
	xmhfhwm_cpu_gprs_ebx = 5UL;
	xmhfhwm_cpu_gprs_esi = 6UL;
	xmhfhwm_cpu_gprs_edi = 7UL;
	saved_cpu_gprs_ebx = xmhfhwm_cpu_gprs_ebx;
	saved_cpu_gprs_esi = xmhfhwm_cpu_gprs_esi;
	saved_cpu_gprs_edi = xmhfhwm_cpu_gprs_edi;
}

void cabi_check(void){
	//@ assert saved_cpu_gprs_ebx == xmhfhwm_cpu_gprs_ebx;
	//@ assert saved_cpu_gprs_esi == xmhfhwm_cpu_gprs_esi;
	//@ assert saved_cpu_gprs_edi == xmhfhwm_cpu_gprs_edi;
}


void drv_bsrl(void){
	uint32_t param1=framac_nondetu32();
	uint32_t result;
	cabi_establish();
        result = CASM_FUNCCALL(bsrl, param1);
	cabi_check();
}

void drv_cpuid(void){
	u32 eax = framac_nondetu32();
	u32 ebx = framac_nondetu32();
	u32 ecx = framac_nondetu32();
	u32 edx = framac_nondetu32();
	u32 op = framac_nondetu32();
	cabi_establish();
	CASM_FUNCCALL(xmhfhw_cpu_cpuid, op, &eax, &ebx, &ecx, &edx);
	cabi_check();
}

void drv_disableintr(void){
	cabi_establish();
	CASM_FUNCCALL(xmhfhw_cpu_disable_intr, CASM_NOPARAM);
	cabi_check();
}

void drv_enableintr(void){
	cabi_establish();
	CASM_FUNCCALL(enable_intr, CASM_NOPARAM);
	cabi_check();
}

void drv_getgdtbase(void){
	u64 result;
	cabi_establish();
	result = CASM_FUNCCALL(xmhf_baseplatform_arch_x86_getgdtbase, CASM_NOPARAM);
	cabi_check();
}

void drv_getidtbase(void){
	u64 result;
	cabi_establish();
	result = CASM_FUNCCALL(xmhf_baseplatform_arch_x86_getidtbase, CASM_NOPARAM);
	cabi_check();
}

void drv_getsec(void){
	u32 eax=0, ebx=0, ecx=0, edx=0;
	cabi_establish();
	CASM_FUNCCALL(xmhfhw_cpu_getsec, &eax, &ebx, &ecx, &edx);
	cabi_check();
}

void drv_gettssbase(void){
	u64 result;
	cabi_establish();
	result = CASM_FUNCCALL(xmhf_baseplatform_arch_x86_gettssbase, CASM_NOPARAM);
	cabi_check();
}

void drv_inb(void){
	u8 result;
	u32 port=framac_nondetu32();
	cabi_establish();
	result = CASM_FUNCCALL(inb, port);
	cabi_check();
}

void drv_inl(void){
	u32 result;
	u32 port=framac_nondetu32();
	cabi_establish();
	result = CASM_FUNCCALL(inl, port);
	cabi_check();
}

void drv_invept(void){
	cabi_establish();
	CASM_FUNCCALL(__vmx_invept, framac_nondetu32(), framac_nondetu32(), framac_nondetu32(), framac_nondetu32());
	cabi_check();
}

void drv_invvpid(void){
	cabi_establish();
	CASM_FUNCCALL(__vmx_invvpid, framac_nondetu32(), framac_nondetu32(), framac_nondetu32());
	cabi_check();
}

void drv_inw(void){
	u16 result;
	u32 port=framac_nondetu32();
	cabi_establish();
	result = CASM_FUNCCALL(inw, port);
	cabi_check();
}

void drv_loadgdt(void){
	arch_x86_gdtdesc_t gdtdesc;
	gdtdesc.base = 0;
	gdtdesc.size = 0;
	cabi_establish();
	CASM_FUNCCALL(xmhfhw_cpu_loadGDT, &gdtdesc);
	cabi_check();
}

void drv_loadidt(void){
	arch_x86_idtdesc_t idtdesc;
	idtdesc.base = 0;
	idtdesc.size = 0;
	cabi_establish();
	CASM_FUNCCALL(xmhfhw_cpu_loadIDT, &idtdesc);
	cabi_check();
}

void drv_loadtr(void){
	u32 trsel=0;
	cabi_establish();
	CASM_FUNCCALL(xmhfhw_cpu_loadTR, trsel);
	cabi_check();
}

void drv_outb(void){
	u32 port=framac_nondetu32();
	cabi_establish();
	CASM_FUNCCALL(outb, framac_nondetu32(), port);
	cabi_check();
}

void drv_outl(void){
	u32 port=framac_nondetu32();
	cabi_establish();
	CASM_FUNCCALL(outl, framac_nondetu32(), port);
	cabi_check();
}

void drv_outw(void){
	u32 port=framac_nondetu32();
	cabi_establish();
	CASM_FUNCCALL(outw, framac_nondetu32(), port);
	cabi_check();
}

void drv_pause(void){
	cabi_establish();
	CASM_FUNCCALL(cpu_relax, CASM_NOPARAM);
	cabi_check();
}

void drv_rdmsr(void){
	u64 result;
	cabi_establish();
	result = CASM_FUNCCALL(rdmsr64, framac_nondetu32());
	cabi_check();
}

void drv_rdtsc(void){
	u64 result;
	cabi_establish();
	result = CASM_FUNCCALL(rdtsc64, CASM_NOPARAM);
	cabi_check();
}

void drv_readcr0(void){
	u64 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_cr0, CASM_NOPARAM);
	cabi_check();
}

void drv_readcr2(void){
	u32 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_cr2, CASM_NOPARAM);
	cabi_check();
}

void drv_readcr3(void){
	u64 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_cr3, CASM_NOPARAM);
	cabi_check();
}

void drv_readcr4(void){
	u64 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_cr4, CASM_NOPARAM);
	cabi_check();
}


void drv_readcs(void){
	u32 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_segreg_cs, CASM_NOPARAM);
	cabi_check();
}

void drv_readds(void){
	u32 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_segreg_ds, CASM_NOPARAM);
	cabi_check();
}

void drv_reades(void){
	u32 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_segreg_es, CASM_NOPARAM);
	cabi_check();
}

void drv_readfs(void){
	u32 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_segreg_fs, CASM_NOPARAM);
	cabi_check();
}

void drv_readgs(void){
	u32 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_segreg_gs, CASM_NOPARAM);
	cabi_check();
}

void drv_readss(void){
	u32 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_segreg_ss, CASM_NOPARAM);
	cabi_check();
}

void drv_readeflags(void){
	u32 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_eflags, CASM_NOPARAM);
	cabi_check();
}

void drv_readesp(void){
	u32 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_esp, CASM_NOPARAM);
	cabi_check();
}

void drv_readrsp(void){
	u64 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_rsp, CASM_NOPARAM);
	cabi_check();
}


void drv_readtr(void){
	u32 result;
	cabi_establish();
	result = CASM_FUNCCALL(read_tr_sel, CASM_NOPARAM);
	cabi_check();
}


static u32 smplock = 1;

void drv_spinlock(void){
	cabi_establish();
	CASM_FUNCCALL(spin_lock, &smplock);
	cabi_check();
}

void drv_spinunlock(void){
	cabi_establish();
	CASM_FUNCCALL(spin_unlock, &smplock);
	cabi_check();
}

u8 buf_vmcs[128];
u8 buf_vmxon[128];

void drv_vmclear(void){
	cabi_establish();
	CASM_FUNCCALL(__vmx_vmclear, (u64)&buf_vmcs);
	cabi_check();
}

void drv_vmptrld(void){
	cabi_establish();
	CASM_FUNCCALL(__vmx_vmptrld, (u64)&buf_vmcs);
	cabi_check();
}

void drv_vmread(void){
	u32 result;
	cabi_establish();
	result = CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread, framac_nondetu32());
	cabi_check();
}

void drv_vmwrite(void){
	cabi_establish();
	CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite, framac_nondetu32(), framac_nondetu32());
	cabi_check();
}

void drv_vmxon(void){
	cabi_establish();
	CASM_FUNCCALL(__vmx_vmxon, (u64)&buf_vmxon);
	cabi_check();
}


void drv_wbinvd(void){
	cabi_establish();
	CASM_FUNCCALL(wbinvd, CASM_NOPARAM);
	cabi_check();
}

void drv_writecr0(void){
	cabi_establish();
	CASM_FUNCCALL(write_cr0, framac_nondetu32());
	cabi_check();
}

void drv_writecr3(void){
	cabi_establish();
	CASM_FUNCCALL(write_cr3, framac_nondetu32());
	cabi_check();
}

void drv_writecr4(void){
	cabi_establish();
	CASM_FUNCCALL(write_cr4, framac_nondetu32());
	cabi_check();
}

void drv_writeeflags(void){
	cabi_establish();
	CASM_FUNCCALL(write_eflags, framac_nondetu32());
	cabi_check();
}

void drv_wrmsr(void){
	cabi_establish();
	CASM_FUNCCALL(wrmsr64, framac_nondetu32(), framac_nondetu32(), framac_nondetu32());
	cabi_check();
}

void drv_xgetbv(void){
	u64 result;
	cabi_establish();
	result = CASM_FUNCCALL(xgetbv, 1);
	cabi_check();
}

void drv_xsetbv(void){
	cabi_establish();
	CASM_FUNCCALL(xsetbv, 1, framac_nondetu32(), framac_nondetu32());
	cabi_check();
}

u8 sysmem_src[128], sysmem_dst[128];

void drv_sysmemaccess_bcopy(void){
	cabi_establish();
	CASM_FUNCCALL(xmhfhw_sysmemaccess_copy, &sysmem_dst, &sysmem_src, sizeof(sysmem_dst));
	cabi_check();
}

void drv_sysmemaccess_readu8(void){
	u8 result;
	cabi_establish();
	result = CASM_FUNCCALL(xmhfhw_sysmemaccess_readu8, &sysmem_dst);
	cabi_check();
}

void drv_sysmemaccess_readu16(void){
	u16 result;
	cabi_establish();
	result = CASM_FUNCCALL(xmhfhw_sysmemaccess_readu16, &sysmem_dst);
	cabi_check();
}

void drv_sysmemaccess_readu32(void){
	u32 result;
	cabi_establish();
	result = CASM_FUNCCALL(xmhfhw_sysmemaccess_readu32, &sysmem_dst);
	cabi_check();
}

void drv_sysmemaccess_readu64(void){
	u64 result;
	cabi_establish();
	result = CASM_FUNCCALL(xmhfhw_sysmemaccess_readu64, &sysmem_dst);
	cabi_check();
}


void drv_sysmemaccess_writeu8(void){
	cabi_establish();
	CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu8, &sysmem_dst, (u8)framac_nondetu32());
	cabi_check();
}

void drv_sysmemaccess_writeu16(void){
	cabi_establish();
	CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu16, &sysmem_dst, (u16)framac_nondetu32());
	cabi_check();
}

void drv_sysmemaccess_writeu32(void){
	cabi_establish();
	CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu32, &sysmem_dst, framac_nondetu32());
	cabi_check();
}

void drv_sysmemaccess_writeu64(void){
	cabi_establish();
	CASM_FUNCCALL(xmhfhw_sysmemaccess_writeu64, &sysmem_dst, framac_nondetu32(), framac_nondetu32());
	cabi_check();
}

u8 uobj_stack[4096];

void main(void){
	u32 check_esp, check_eip = CASM_RET_EIP;

	//populate hardware model stack and program counter
	xmhfhwm_cpu_gprs_esp = &uobj_stack[4096];
	xmhfhwm_cpu_gprs_eip = check_eip;
	check_esp = xmhfhwm_cpu_gprs_esp; // pointing to top-of-stack

	//execute harness: TODO
	//drv_bsrl();
	//drv_cpuid();
	//drv_disableintr();
	//drv_enableintr();
	//drv_getgdtbase();
	//drv_getidtbase();
	//drv_getsec();
	//drv_gettssbase();
	//drv_inb();
	//drv_inl();
	//drv_invept();
	//drv_invvpid();
	//drv_inw();
	//drv_loadgdt();
	//drv_loadidt();
	//drv_loadtr();
	//drv_outb();
	//drv_outl();
	//drv_outw();
	//drv_pause();
	//drv_rdmsr();
	//drv_rdtsc();
	//drv_readcr0();
	//drv_readcr2();
	//drv_readcr3();
	//drv_readcr4();
	//drv_readcs();
	//drv_readds();
	//drv_reades();
	//drv_readfs();
	//drv_readgs();
	//drv_readss();
	//drv_readeflags();
	//drv_readesp();
	//drv_readrsp();
	//drv_readtr();
	//drv_spinlock();
	//drv_spinunlock();
	//drv_vmclear();
	//drv_vmptrld();
	//drv_vmread();
	//drv_vmwrite();
	//drv_vmxon();
        //drv_wbinvd();
        //drv_writecr0();
        //drv_writecr3();
        //drv_writecr4();
	//drv_writeeflags();
	//drv_wrmsr();
	//drv_xgetbv();
	//drv_xsetbv();
	//drv_sysmemaccess_bcopy();
	//drv_sysmemaccess_readu8();
	//drv_sysmemaccess_readu16();
	//drv_sysmemaccess_readu32();
	//drv_sysmemaccess_readu64();
	//drv_sysmemaccess_writeu8();
	//drv_sysmemaccess_writeu16();
	//drv_sysmemaccess_writeu32();
	//drv_sysmemaccess_writeu64();

	//@assert xmhfhwm_cpu_gprs_esp == check_esp;
	//@assert xmhfhwm_cpu_gprs_eip == check_eip;
}


