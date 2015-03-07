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


void xmhfhw_cpu_cpuid(u32 op, u32 *eax, u32 *ebx, u32 *ecx, u32 *edx){
    asm volatile(
                 "cpuid \r\n"
                :"=a"(*(eax)), "=b"(*(ebx)), "=c"(*(ecx)), "=d"(*(edx))
                :"a"(op), "c"(*(ecx))
                :
               );


}


uint64_t rdtsc64(void)
{
        uint64_t rv;

        __asm__ __volatile__ ("rdtsc" : "=A" (rv));
        return (rv);
}


/* Calls to read and write control registers */
u64 read_cr0(void){
  u64 __cr0;
  asm volatile("mov %%cr0,%0 \r\n" :"=r" (__cr0));
  return __cr0;
}

void write_cr0(u64 val){
  asm volatile("mov %0,%%cr0 \r\n": :"r" (val));
}

u32 read_cr2(void){
  u32 __cr2;
  asm volatile("mov %%cr2,%0 \r\n" :"=r" (__cr2));
  return __cr2;
}

u64 read_cr3(void){
  u64 __cr3;
  asm volatile("mov %%cr3,%0 \r\n" :"=r" (__cr3));
  return __cr3;
}


u64 read_rsp(void){
  u64 __rsp;
/*
  // TODO: x86_64 --> x86
  asm volatile("movq %%rsp,%0\n\t" :"=r" (__rsp));
*/

  return __rsp;
}

u32 read_esp(void){
  u32 __esp;
  asm volatile("mov %%esp,%0\n\t" :"=r" (__esp));
  return __esp;
}

void write_cr3(u64 val){
  asm volatile("mov %0,%%cr3 \r\n"::"r" (val));
}

u64 read_cr4(void){
  u64 __cr4;
  asm volatile("mov %%cr4, %0 \r\n" :"=r" (__cr4));
  return __cr4;
}

void write_cr4(u64 val){
  asm volatile("mov %0,%%cr4": :"r" (val));
}


/*void skinit(unsigned long eax) {
    __asm__("mov %0, %%eax": :"r" (eax));
    __asm__("skinit %%eax":);
}*/


//segment register access
u32 read_segreg_cs(void){
  u32 __cs;
  __asm__("mov %%cs, %0 \r\n" :"=r" (__cs));
  return __cs;
}

u32 read_segreg_ds(void){
  u32 __ds;
  __asm__("mov %%ds, %0 \r\n" :"=r" (__ds));
  return __ds;
}

u32 read_segreg_es(void){
  u32 __es;
  __asm__("mov %%es, %0 \r\n" :"=r" (__es));
  return __es;
}

u32 read_segreg_fs(void){
  u32 __fs;
  __asm__("mov %%fs, %0 \r\n" :"=r" (__fs));
  return __fs;
}

u32 read_segreg_gs(void){
  u32 __gs;
  __asm__("mov %%gs, %0 \r\n" :"=r" (__gs));
  return __gs;
}

u32 read_segreg_ss(void){
  u32 __ss;
  __asm__("mov %%ss, %0 \r\n" :"=r" (__ss));
  return __ss;
}

u16 read_tr_sel(void){
  u16 __trsel;
  __asm__("str %0 \r\n" :"=r" (__trsel));
  return __trsel;
}

void wbinvd(void)
{
    __asm__ __volatile__ ("wbinvd");
}

uint32_t bsrl(uint32_t mask)
{
    uint32_t   result;

    __asm__ __volatile__ ("bsrl %1,%0" : "=r" (result) : "rm" (mask) : "cc");
    return (result);
}


void xmhfhw_cpu_disable_intr(void){
    asm volatile ("cli \r\n");
}

void enable_intr(void)
{
    __asm__ __volatile__ ("sti");
}

//get extended control register (xcr)
u64 xgetbv(u32 xcr_reg){
	u32 eax, edx;

	asm volatile(".byte 0x0f,0x01,0xd0"
			: "=a" (eax), "=d" (edx)
			: "c" (xcr_reg));

	return ((u64)edx << 32) + (u64)eax;
}

//set extended control register (xcr)
void xsetbv(u32 xcr_reg, u64 value){
	u32 eax = (u32)value;
	u32 edx = value >> 32;

	asm volatile(".byte 0x0f,0x01,0xd1"
			:
			: "a" (eax), "d" (edx), "c" (xcr_reg));
}


void sysexitq(u64 rip, u64 rsp){

/*
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
*/

}


void spin_lock(volatile u32 *lock){
        __asm__ __volatile__ (
            "1:	btl	$0, %0	\r\n"	//mutex is available?
            "		jnc 1b	\r\n"	//wait till it is
            "      	lock		\r\n"   //lock the bus (exclusive access)
            "		btrl	$0, %0	\r\n"   //and try to grab the mutex
            "		jnc	1b	\r\n"   //spin until successful --> spinlock :p
            : //no asm outputs
            : "m" (*lock)
        );
    }

void spin_unlock(volatile u32 *lock){
        __asm__ __volatile__ (
            "btsl	$0, %0		\r\n"	//release spinlock
            : //no asm outputs
            : "m" (*lock)
        );
    }

//load CPU GDT
void xmhfhw_cpu_loadGDT(arch_x86_gdtdesc_t *gdt_addr){

	asm volatile(
		"lgdt  %0 \r\n"
		: //no outputs
		: "m" (*gdt_addr)
		:
	);

}

//load CPU TR
void xmhfhw_cpu_loadTR(u32 tr_selector){

	  asm volatile(
		"movl %0, %%eax\r\n"
		"ltr %%ax\r\n"				//load TR
	     :
	     : "g"(tr_selector)
	     : "eax"
	  );

}

//load CPU IDT
void xmhfhw_cpu_loadIDT(arch_x86_idtdesc_t *idt_addr){

	asm volatile(
		"lidt  %0 \r\n"
		: //no outputs
		: "m" (*idt_addr)
		: //no clobber
	);

}


u64 xmhf_baseplatform_arch_x86_getgdtbase(void){
		struct {
			u16 limit;
			u64 base;
		} __attribute__ ((packed)) gdtr;


		asm volatile(
			"sgdt %0 \r\n"
			: //no output
			: "m" (gdtr)
			: //no clobber
		);

		return gdtr.base;
}

u64 xmhf_baseplatform_arch_x86_getidtbase(void){
		struct {
			u16 limit;
			u64 base;
		} __attribute__ ((packed)) idtr;


		asm volatile(
			"sidt %0 \r\n"
			: //no output
			: "m" (idtr)
			: //no clobber
		);

		return idtr.base;
}

u64  xmhf_baseplatform_arch_x86_gettssbase(void){
	  u64 gdtbase = xmhf_baseplatform_arch_x86_getgdtbase();
	  u32 tssdesc_low, tssdesc_high;

	  asm volatile(
            "movl %2, %%edi\r\n"
            "xorl %%eax, %%eax\r\n"
            "str %%ax \r\n"
            "addl %%eax, %%edi\r\n"		//%edi is pointer to TSS descriptor in GDT
            "movl (%%edi), %0 \r\n"		//move low 32-bits of TSS descriptor into tssdesc_low
            "addl $0x4, %%edi\r\n"		//%edi points to top 32-bits of 64-bit TSS desc.
            "movl (%%edi), %1 \r\n"		//move high 32-bits of TSS descriptor into tssdesc_high
	     : "=r" (tssdesc_low), "=r" (tssdesc_high)
	     : "m"(gdtbase)
	     : "edi", "eax"
	  );

       return (  (u64)(  ((u32)tssdesc_high & 0xFF000000UL) | (((u32)tssdesc_high & 0x000000FFUL) << 16)  | ((u32)tssdesc_low >> 16)  ) );
}















