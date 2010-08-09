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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

//------------------------------------------------------------------------------
//v86monitor.c
//
// intel v8086 monitor to run real-mode code within v86 for Intel VT
// without support for "unrestricted guest" bit
//
// author: amit vasudevan (amitvasudevan@acm.org)

#include <target.h>

//---globals and externs--------------------------------------------------------
extern PXTLPB lpb;

extern u32 __runtime_v86_pagedir[], __runtime_v86_pagetables[]; 
extern u32 __runtime_v86_idt[], __runtime_v86_idtfunctionptrs[];
extern void __v86_gpfh_stub(void);
extern u32 __runtime_v86_gdt[], __runtime_v86_ldt[], __runtime_v86_tss[];
extern u32 __runtime_v86_ring0stack[];

//note for v86 mode
//setting CR4.VME=0 and EFLAGS.IOPL=3
//every interrupt, either s/w or h/w goes through prot mode IDT
//ensure DPL=3 for all IDT handlers
//GPF (INT 0Dh) is invoked on instructions such as HLT, LMSW etc.
//remember GPF has priority over VM EXIT on VT !!!

u32 v86monitor_guest_gdt_base=0;
u16 v86monitor_guest_gdt_limit=0;
u32 v86monitor_guest_idt_base=0;
u16 v86monitor_guest_idt_limit=0;
u32 v86monitor_guest_reg_cr0= V86M_CR0_INITIALVALUE; 

u32 v86monitor_guest_reg_eax=0;
u32 v86monitor_guest_reg_ebx=0;
u32 v86monitor_guest_reg_ecx=0;
u32 v86monitor_guest_reg_edx=0;
u32 v86monitor_guest_reg_esi=0;
u32 v86monitor_guest_reg_edi=0;
u32 v86monitor_guest_reg_ebp=0;
u32 v86monitor_guest_reg_esp=0;
u32 v86monitor_guest_reg_eip=0;
u32 v86monitor_guest_reg_cs=0;
u32 v86monitor_guest_reg_ss=0;
u32 v86monitor_guest_reg_eflags=0;
u32 v86monitor_guest_reg_cr4=0;
u32 v86monitor_guest_reg_cr3=0;

void v86_gpfh(u32 *stack){
	INTRREGS *i = (INTRREGS *)stack;
	FAULTFRAME *f;
	u32 paddr;
	
	//printf("\nGPFH: ESP=0x%08lx", i->esp);
	f = (FAULTFRAME *)i->esp;
	//printf("\nCS=0x%04x, EIP=0x%08lx", (u16)f->cs, f->eip);
	paddr = ((u16)f->cs * 16) + (u16)f->eip;

	/*printf("\nDump:\n");
	{
		u32 i;
		u8 *p=(u8 *)paddr;
		for(i=0; i < 16; i++)
			printf("0x%02x ", p[i]);
	}
	HALTV86M();*/

	//we need to handle mov to/from all DR registers -- passthru
	//move to/from CR3 needs to be handled
	//move to/from CR4 needs to be handled
	//move to/from CR0 needs to be handled
	//rest moves to/from CRx -- passthru
	//move to CR0 with PE bit set == End of V86 session, cause world switch
	//LGDT and LIDT need to be handled
	
	{
		u8 *pc = (u8 *)paddr;
		
		if(pc[0] == 0x0F && pc[1] == 0x01){
			if( ((pc[2] & (u8)0x38) >> 3) == 2){
				//LGDT 16-bit mem relative to DS
				u16 offset = *((u16 *)&pc[3]);
				u32 lgdtpaddr = ((f->ds * 16) + (u32)offset);
				v86monitor_guest_gdt_limit = *((u16 *)lgdtpaddr);
				v86monitor_guest_gdt_base = *((u32 *)((u32)lgdtpaddr+2));
				//printf("\nLGDT decoded: offset=0x%04x, ds=0x%04x, lgdtpaddr=0x%08lx",
				//		offset, (u16)f->ds, (unsigned long)lgdtpaddr);
				//printf("\n              guest_gdt_base=0x%08lx, guest_gdt_limit=0x%04x",
				//			(unsigned long)v86monitor_guest_gdt_base, (u16)v86monitor_guest_gdt_limit);
				f->eip += 5;
				return;	
			}else if( ((pc[2] & (u8)0x38) >> 3) == 3){
				//LIDT 16-bit mem relative to DS
				u16 offset = *((u16 *)&pc[3]);
				u32 lidtpaddr = ((f->ds * 16) + (u32)offset);
				v86monitor_guest_idt_limit = *((u16 *)lidtpaddr);
				v86monitor_guest_idt_base = *((u32 *)((u32)lidtpaddr+2));
				//printf("\nLIDT decoded: offset=0x%04x, ds=0x%04x, lidtpaddr=0x%08lx",
				//		offset, (u16)f->ds, (unsigned long)lidtpaddr);
				//printf("\n              guest_idt_base=0x%08lx, guest_idt_limit=0x%04x",
				//		(unsigned long)v86monitor_guest_idt_base, (u16)v86monitor_guest_idt_limit);
				f->eip += 5;
				return;	
			}else{
				printf("\npanic: unhandled LGDT/LIDT instruction format!");
				HALTV86M();			
			}
		}
		
		//handle 32-bit variant of LGDT
		if(pc[0] == 0x67 && pc[1] == 0x66 && pc[2] == 0x0F && pc[3] == 0x01){
			if( ((pc[4] & (u8)0x38) >> 3) == 2){
				//LGDT 16-bit mem relative to DS
				u32 offset = *((u32 *)&pc[5]);
				u32 lgdtpaddr = ((f->ds * 16) + (u32)offset);
				v86monitor_guest_gdt_limit = *((u16 *)lgdtpaddr);
				v86monitor_guest_gdt_base = *((u32 *)((u32)lgdtpaddr+2));
				//printf("\nLGDT decoded(32-bit): offset=0x%08x, ds=0x%04x, lgdtpaddr=0x%08lx",
				//		offset, (u16)f->ds, (unsigned long)lgdtpaddr);
				//printf("\n              guest_gdt_base=0x%08lx, guest_gdt_limit=0x%04x",
				//			(unsigned long)v86monitor_guest_gdt_base, (u16)v86monitor_guest_gdt_limit);
				f->eip += 7;
				return;	
			}
		}
		
		//handle another variant of LGDT/LIDT
		if(pc[0] == 0x66 && pc[1] == 0x0F && pc[2] == 0x01){
			if( ((pc[3] & (u8)0x38) >> 3) == 2){
				//LGDT 16-bit mem relative to DS
				u16 offset = *((u16 *)&pc[4]);
				u32 lgdtpaddr = ((f->ds * 16) + (u32)offset);
				v86monitor_guest_gdt_limit = *((u16 *)lgdtpaddr);
				v86monitor_guest_gdt_base = *((u32 *)((u32)lgdtpaddr+2));
				//printf("\nLGDT decoded: offset=0x%04x, ds=0x%04x, lgdtpaddr=0x%08lx",
				//		offset, (u16)f->ds, (unsigned long)lgdtpaddr);
				//printf("\n              guest_gdt_base=0x%08lx, guest_gdt_limit=0x%04x",
				//					(unsigned long)v86monitor_guest_gdt_base, (u16)v86monitor_guest_gdt_limit);
				f->eip += 6;
				return;	
			}else if( ((pc[3] & (u8)0x38) >> 3) == 3){
				//LIDT 16-bit mem relative to DS
				u16 offset = *((u16 *)&pc[4]);
				u32 lidtpaddr = ((f->ds * 16) + (u32)offset);
				v86monitor_guest_idt_limit = *((u16 *)lidtpaddr);
				v86monitor_guest_idt_base = *((u32 *)((u32)lidtpaddr+2));
				//printf("\nLIDT decoded: offset=0x%04x, ds=0x%04x, lidtpaddr=0x%08lx",
				//		offset, (u16)f->ds, (unsigned long)lidtpaddr);
				//printf("\n              guest_idt_base=0x%08lx, guest_idt_limit=0x%04x",
				//					(unsigned long)v86monitor_guest_idt_base, (u16)v86monitor_guest_idt_limit);
				f->eip += 6;
				return;	
			}else{
				printf("\npanic: unhandled LGDT/LIDT instruction format with 0x66 prefix!");
				HALTV86M();			
			}
		}
		
		if(pc[0] == 0x0f && pc[1] == 0x20){
			//MOV from CRx
			u8 crx = (pc[2] & (u8)0x38) >> (u8)3;
			u8 reg = (pc[2] & (u8)0x07);
			//crx contains the control register and reg contains the GPR
			if(crx == 0 && reg == 0){
				//MOV EAX, CR0
				//printf("\nMOV EAX, CR0 decoded, EAX=0x%08lx", (unsigned long)v86monitor_guest_reg_cr0);
				i->eax = v86monitor_guest_reg_cr0;
				f->eip += 3;
				return;
			}else if(crx == 0 && reg == 2){
				//MOV EDX, CR0
				//printf("\nMOV EDX, CR0 decoded, EDX=0x%08lx", (unsigned long)v86monitor_guest_reg_cr0);
				i->edx = v86monitor_guest_reg_cr0;
				f->eip += 3;
				return;
			}else if (crx == 3 && reg == 0){
				//MOV EAX, CR3
				//printf("\nMOV EAX, CR3 decoded, EAX=0x%08lx", (unsigned long)v86monitor_guest_reg_cr3);
				i->eax = v86monitor_guest_reg_cr3;
				f->eip += 3;
				return;
			}else{
				printf("\npanic: unhandled MOV from CRX, crx=0x%02x, reg=0x%02x", 
					crx, reg);
				HALTV86M();
			}		
		
		}
		
		//RDMSR (this will cause another trap into islayer which will do the
		//actual reading)
		if(pc[0] == 0x0f && pc[1] == 0x32){
				asm volatile ("rdmsr\r\n"
          		: "=a"(i->eax), "=d"(i->edx)
          		: "c" (i->ecx));
				f->eip +=2;
				return;
		}
		
		
		if(pc[0] == 0x0f && pc[1] == 0x22){
			//MOV to CRx
			u8 crx = (pc[2] & (u8)0x38) >> (u8)3;
			u8 reg = (pc[2] & (u8)0x07);
			//crx contains the control register and reg contains the GPR
			if( (crx == 0 && reg == 0) || (crx == 0 && reg == 0x2) ){
				//MOV CR0, EAX or MOV CR0, EDX
				//printf("\nHALT! MOV CR0, EAX decoded, EAX=0x%08lx", i->eax);
				if(crx == 0 && reg == 0){
					v86monitor_guest_reg_cr0 = i->eax;
				}else if (crx == 0 && reg == 2){
					v86monitor_guest_reg_cr0 = i->edx;
				}else{
					printf("\nunhanled MOVE to CR0..HALT!");
					HALTV86M();
				}
				
				
				f->eip += 3;
				if(v86monitor_guest_reg_cr0 & (u32)CR0_PE){
					//store all GPR contents, CS:EIP and SS
					v86monitor_guest_reg_eax=i->eax;
					v86monitor_guest_reg_ebx=i->ebx;
					v86monitor_guest_reg_ecx=i->ecx;
					v86monitor_guest_reg_edx=i->edx;
					v86monitor_guest_reg_esi=i->esi;
					v86monitor_guest_reg_edi=i->edi;
					v86monitor_guest_reg_ebp=i->ebp;
					v86monitor_guest_reg_esp=f->esp;
					v86monitor_guest_reg_eip=f->eip;
					v86monitor_guest_reg_ss=f->ss;
					v86monitor_guest_reg_cs=f->cs;
					v86monitor_guest_reg_eflags=f->eflags;
					asm("mov %%cr4, %%eax \n mov %%eax, v86monitor_guest_reg_cr4" 
							::: "ax" );
					__asm__ __volatile__ ("hlt \r\n");
					//this causes a world switch to our hypervisor
				}
			}else if(crx == 3 && reg == 0){
				//MOV CR3, EAX
				//printf("\nDecoded MOV CR3, EAX..");
				v86monitor_guest_reg_cr3 = i->eax;
				/*asm volatile ("movl %%cr3, %%eax\r\n"
											"movl %%eax, %%cr3\r\n"
											: //no outputs
											: //no inputs
											: "%eax" 
											);*/
				f->eip +=3;
				return;
			}else{
				printf("\npanic: unhandled MOV from CRX, crx=0x%02x, reg=0x%02x", crx, reg);
				HALTV86M();
			}		
		
		}
		
	}
	

	printf("\npanic: unhandled instruction!");
  printf("\nCS=0x%04x, EIP=0x%08lx", (u16)f->cs, f->eip);
	printf("\nDump:\n");
	paddr = ((u16)f->cs * 16) + (u16)f->eip;
	{
		u32 i;
		u8 *p=(u8 *)paddr;
		for(i=0; i < 16; i++)
			printf("0x%02x ", p[i]);
	}
	HALTV86M();

}


//------------------------------------------------------------------------------
// INT 15h, E820 handler
/*
typedef struct {
	u32 baseaddrlow;
	u32 baseaddrhigh;
	u32 lengthlow;
	u32 lengthhigh;
	u32 type;
} __attribute__((packed)) E820ARD;


//e820 map of VTBOX (supermicro)
E820ARD e820map[]={
	{0x00000000, 0x00000000, 0x0009fc00, 0x0, 0x1},
	{0x0009fc00, 0x00000000, 0x00000400, 0x0, 0x2},
	{0x000e0000, 0x00000000, 0x00020000, 0x0, 0x2},
//	{0x00100000, 0x00000000, 0xBF680000, 0x0, 0x1},
	{0x00100000, 0x00000000, 0x1FF00000, 0x0, 0x1},
	{0x20000000, 0x00000000, 0x9F780000, 0x0, 0x2},
	
	{0xbf78e000, 0x00000000, 0x00002000, 0x0, 0x9},
	{0xbf790000, 0x00000000, 0x0000e000, 0x0, 0x3},
	{0xbf79e000, 0x00000000, 0x00032000, 0x0, 0x4},
	{0xbf7d0000, 0x00000000, 0x00010000, 0x0, 0x2},
	{0xbf7ec000, 0x00000000, 0x00814000, 0x0, 0x2},
	{0xfee00000, 0x00000000, 0x00400000, 0x0, 0x2},
	{0x00000000, 0x00000001, 0x40000000, 0x0, 0x2}
};
u32 max_e820map_index=12;
*/


/*
//	e820 map of HP laptop (NPT)
E820ARD e820map[]={
	{0x00000000, 0x00000000, 0x0009fc00, 0x0, 0x1},
	{0x0009fc00, 0x00000000, 0x00000400, 0x0, 0x2},
	{0x000ef000, 0x00000000, 0x00011000, 0x0, 0x2},
	{0x00100000, 0x00000000, 0xbf4a7000, 0x0, 0x1},
	{0xbf5a7000, 0x00000000, 0x0011b000, 0x0, 0x2},
	{0xbf6c2000, 0x00000000, 0x00100000, 0x0, 0x4},
	{0xbf7c2000, 0x00000000, 0x0003d000, 0x0, 0x3},
	{0xbf7ff000, 0x00000000, 0x00001000, 0x0, 0x1},
	{0xbf800000, 0x00000000, 0x00800000, 0x0, 0x2},
	{0xe0000000, 0x00000000, 0x10000000, 0x0, 0x2},
	{0xfec00000, 0x00000000, 0x00001000, 0x0, 0x2},
	{0xfed10000, 0x00000000, 0x00004000, 0x0, 0x2},
	{0xfed19000, 0x00000000, 0x00001000, 0x0, 0x2},
	{0xfed1b000, 0x00000000, 0x00005000, 0x0, 0x2},
	{0xfee00000, 0x00000000, 0x00001000, 0x0, 0x2},
	{0xffd00000, 0x00000000, 0x00300000, 0x0, 0x2},
	{0x00000000, 0x1, 0x38000000, 0x0, 0x1}
};	
	
u32 max_e820map_index=17;
*/

/*
//e820 map of HP Laptop (ADAMS)
E820ARD e820map[]={
	{0x00000000, 0x00000000, 0x0009fc00, 0x0, 0x1},
	{0x0009fc00, 0x00000000, 0x00000400, 0x0, 0x2},
	{0x000ef000, 0x00000000, 0x00020000, 0x0, 0x2},
//	{0x00100000, 0x00000000, 0xB8E43000, 0x0, 0x1},
	{0x00100000, 0x00000000, 0x3FF00000, 0x0, 0x1},
	{0x40000000, 0x00000000, 0x78F43000, 0x0, 0x2},
//	{0x00100000, 0x00000000, 0x7FF00000, 0x0, 0x1},
//	{0x80000000, 0x00000000, 0x38F43000, 0x0, 0x2},


	{0xb8f43000, 0x00000000, 0x00002000, 0x0, 0x2},
//	{0xb8f45000, 0x00000000, 0x00e2b000, 0x0, 0x1},
		{0xb8f45000, 0x00000000, 0x00e2b000, 0x0, 0x2},
		
	{0xb9d70000, 0x00000000, 0x00e10000, 0x0, 0x3},
//	{0xb9d80000, 0x00000000, 0x02743000, 0x0, 0x1},
	{0xb9d80000, 0x00000000, 0x02743000, 0x0, 0x2},

	{0xbc4c3000, 0x00000000, 0x00200000, 0x0, 0x3},

	//{0xbc6c3000, 0x00000000, 0x017CF000, 0x0, 0x1},
	{0xbc6c3000, 0x00000000, 0x017CF000, 0x0, 0x2},

	{0xbde92000, 0x00000000, 0x00008000, 0x0, 0x2},
	//{0xbde9a000, 0x00000000, 0x00025000, 0x0, 0x1},
	{0xbde9a000, 0x00000000, 0x00025000, 0x0, 0x2},
	
	{0xbdebf000, 0x00000000, 0x00010000, 0x0, 0x2},
	{0xbdecf000, 0x00000000, 0x00100000, 0x0, 0x3},
	{0xbdfcf000, 0x00000000, 0x00030000, 0x0, 0x4},
	//{0xbdfff000, 0x00000000, 0x00001000, 0x0, 0x1},
	{0xbdfff000, 0x00000000, 0x00001000, 0x0, 0x2},
	
	{0xbe000000, 0x00000000, 0x20000000, 0x0, 0x2},
	{0xe0000000, 0x00000000, 0x10000000, 0x0, 0x2},
	{0xfec00000, 0x00000000, 0x00001000, 0x0, 0x2},
	{0xfed10000, 0x00000000, 0x00004000, 0x0, 0x2},
	{0xfed18000, 0x00000000, 0x00002000, 0x0, 0x2},
	{0xfed1c000, 0x00000000, 0x00004000, 0x0, 0x2},
	{0xfee00000, 0x00000000, 0x00001000, 0x0, 0x2},
	{0xffe80000, 0x00000000, 0x00180000, 0x0, 0x2},
	
	//{0x00000000, 0x00000001, 0x3c000000, 0x0, 0x1}
	{0x00000000, 0x00000001, 0x3c000000, 0x0, 0x2}
};


u32 max_e820map_index=26;
*/

extern GRUBE820 *grube820list;


void handle_e820(INTRREGS *i, FAULTFRAME *f){

		if(i->edx != 0x534D4150UL){ //'SMAP'
				printf("\nunhandled INT15h E820, invalid signature!");
				HALTV86M();
		}			
			
		//return value, CF=0 indicated no error, EAX='SMAP'
		//ES:DI left untouched, ECX=size returned, EBX=next continuation value
		//EBX=0 if last descriptor
		if(i->ebx > lpb->XtVmmE820NumEntries){
				printf("\ninvalid continuation value specified!");
				HALTV86M();				
		}
			
		//printf("\nECX=%u", i->ecx);
			
		//printf("\nreturning for index=%u", i->ebx);
		//printf("\nES=0x%04X, DI=0x%04X", (u16)f->es, (u16)i->edi);
    memcpy((void *)((f->es * 16)+(u16)i->edi), (void *)&grube820list[i->ebx],
					sizeof(GRUBE820));
		i->ebx=i->ebx+1;
				
				
		i->eax=i->edx;
		i->ecx=20;

		if(i->ebx > lpb->XtVmmE820NumEntries){
					i->ebx=0;	
					f->eflags |= (unsigned long)0x1;
		}else{
					f->eflags &= ~(unsigned long)0x1;
		}

		//printf("\nnext continuation value=%u", i->ebx);

}

//------------------------------------------------------------------------------


void v86_handleinterrupt(unsigned long vector, u32 *stack) __attribute__((cdecl));
void v86_handleinterrupt(unsigned long vector, u32 *stack) {
	INTRREGS *i = (INTRREGS *)stack;
	FAULTFRAME *f;
	
	
	f = (FAULTFRAME *)i->esp;

	//printf("\nINT 0x%08lx: ESP=0x%08lx, CS:EIP=0x%04x:0x%08x", vector, i->esp,
	//	(u16)f->cs, f->eip);

	if(vector == 0x6){
		//invalid opcode
		printf("\nInvalid opcode at CS:EIP=0x%04x:0x%08x", (u16)f->cs, f->eip);
		printf("\ndump at CS:EIP follows:\n");
		{
			u32 i;
			u32 paddr= (f->cs * 16) + f->eip;
			u8 *p=(u8 *)paddr;
			for(i=0; i < 0x10; i++)
				printf("%02x ", p[i]);
		}
		HALTV86M();
	}

	/*if(vector == 0xd){
		printf("\ndump at CS:EIP follows:\n");
		{
			u32 i;
			u32 paddr= (f->cs * 16) + f->eip;
			u8 *p=(u8 *)paddr;
			for(i=0; i < 16; i++)
				printf("%02x ", p[i]);
		}
	}*/

#if !defined(__CONF_GUESTOS_LINUX__) 

	//E820 hook, redirect INT 15, EAX=0xE820 to report lesser memory
	if(vector == 0x15 && i->eax == 0xE820){
		printf("\nE820 request at CS:EIP=0x%04x:0x%08lx", 
			(u16)f->cs, f->eip);
		handle_e820(i, f);
		return;
	}
#endif

	//if(vector == 0x13)
	//	printf("\nDisk request at CS:EIP=0x%04x:0x%08lx", (u16)f->cs, f->eip); 
	
	//printf("\nCS=0x%04x, EIP=0x%08lx", (u16)f->cs, f->eip);
	//printf("\nSS=0x%04x, ESP=0x%08lx", (u16)f->ss, f->esp);
	//printf("\nEFLAGS=0x%08lx", f->eflags);

	//we need to push FLAGS, CS and IP on the stack 
	//and adjust f->cs and f->eip to point to int handler from IVT
	//also adjust f->ss and f->esp in the process
	{
		u32 paddr;
		f->esp = f->esp -2;
		paddr = (f->ss * 16) + (u16)f->esp;
		* ((u16 *)paddr) = (u16)f->eflags;
		f->esp = f->esp -2;
		paddr = (f->ss * 16) + (u16)f->esp;
		* ((u16 *)paddr) = (u16)f->cs;
		f->esp = f->esp -2;
		paddr = (f->ss * 16) + (u16)f->esp;
		* ((u16 *)paddr) = (u16)f->eip;
	}
	 
	f->cs = *(u16 *) (((u32)vector*4)+2);
	f->eip = (u32)(u16)(*(u16 *)((u32)vector*4));

	//printf("\nnew SS:ESP=0x%04x:0x%08lx, CS:EIP=0x%04x:0x%08lx",
	//	(u16)f->ss, f->esp, (u16)f->cs, f->eip);	
	//printf("\ndump at SS:ESP follows:\n");
	//{
	//	u32 i;
	//	u32 paddr= (f->ss * 16) + f->esp;
	//	u8 *p=(u8 *)paddr;
	//	for(i=0; i < 16; i++)
	//		printf("%02x ", p[i]);
	//}
			
}


//---initialize v86monitor and its data structures------------------------------
void v86monitor_initialize(void){
  //initialize v86 mode paging structures
  {
    u32	*pgdir, *pgtbl;
  	u32 i;
  	u32 flags = (u32)(_PAGE_PRESENT | _PAGE_RW | _PAGE_USER);
    				
  	pgdir = (u32 *)__runtime_v86_pagedir;
  	for (i = 0; i < 1024; i++)
  	 pgdir[ i ] = npae_make_pde( __hva2spa__((u32)__runtime_v86_pagetables + (i*4096)), flags);
     		
  	pgtbl = (u32 *)__runtime_v86_pagetables;
  	for (i = 0; i < (1024*1024); i++){
  		u32 page_address = (i << 12); 
  		
      if(page_address >= lpb->XtVmmRuntimePhysBase && page_address < (lpb->XtVmmRuntimePhysBase+lpb->XtVmmRuntimeSize)){
        //map this virtual address to physical memory occupied by runtime virtual range
        u32 offset = page_address - lpb->XtVmmRuntimePhysBase;
        pgtbl[i] = npae_make_pte((u32)lpb->XtVmmRuntimeVirtBase+offset, flags);
      }else if(page_address >= lpb->XtVmmRuntimeVirtBase && page_address < (lpb->XtVmmRuntimeVirtBase+lpb->XtVmmRuntimeSize)){
        //map this virtual addr to runtime physical addr
        u32 offset = page_address - lpb->XtVmmRuntimeVirtBase;
        pgtbl[i] = npae_make_pte((u32)lpb->XtVmmRuntimePhysBase+offset, flags);
      }else{
        //unity map
        if(page_address == 0xfee00000)
          flags |= (u32)(_PAGE_PCD);
        
        pgtbl[i] = npae_make_pte((u32)page_address, flags);
      }
  	}
  }

	//setup v86 mode IDT
	{
		u64 *g_idt;
		u64 desc;
		u32 *fptr;
		u32 i;
		memset((void *)__runtime_v86_idt, 0, 0x1000);
		g_idt = (u64 *)(u32)__runtime_v86_idt;
		fptr = (u32 *)__runtime_v86_idtfunctionptrs;
			
		for(i=0; i < 256; i++){
			if(i==13){
				desc = (u64)(u32)__v86_gpfh_stub; 	// offset for GPF handler
				desc &= 0x00000000FFFFFFFFULL;
				desc |= (desc << 32);
				desc &= 0xFFFF00000000FFFFULL; 
				desc |= (V86M_SELECTOR_CODE << 16);
				desc |= (0xEE00ULL << 32);	// DPL=3, 386-INTR-gate
				g_idt[ 13 ] = desc;		// General Protection Fault		
			}else{
				desc = (u64)(u32)fptr[i]; 	// offset for int stub
				desc &= 0x00000000FFFFFFFFULL;
				desc |= (desc << 32);
				desc &= 0xFFFF00000000FFFFULL; 
				desc |= (V86M_SELECTOR_CODE << 16);
				desc |= (0xEE00ULL << 32);	// DPL=3, 386-INTR-gate
				g_idt[i] = desc;		// INT 		
			}
		}
	}
} 

//---v86monitor setup guest real-mode state----------------------
void v86monitor_initializeguest(VCPU *vcpu){
  //we need to setup LDT, GDT and TSS here as each TSS uses a specific
  //ring 0 stack which cannot be shared between cores. So we give each core 
  //its own LDT, GDT and TSS while working within the V86 monitor

	//setup LDT
	{
		u64 *g_ldt;
		u64 desc;
		memset((void *)__runtime_v86_ldt, 0, 0x1000);
		g_ldt = (u64 *)(u32)__runtime_v86_ldt; //[TODO: grab from vcpu]
		desc = 0x00CF9A000000FFFFLL;
		g_ldt[ V86M_SELECTOR_CODE >> 3 ] = desc;
		desc = 0x00CF92000000FFFFLL;
		g_ldt[ V86M_SELECTOR_DATA >> 3 ] = desc; 
		desc = 0x0000920B8000FFFFLL;
		g_ldt[ V86M_SELECTOR_VRAM >> 3 ] = desc;
		desc = 0x00CF92000000FFFFLL;
		g_ldt[ V86M_SELECTOR_FLAT >> 3 ] = desc;
	}	
  
	//setup GDT
	{
		u64 *g_gdt;
		u64 desc;
		memset((void *)__runtime_v86_gdt, 0, 0x1000); //[TODO: grab from vcpu]
		g_gdt = (u64 *)(u32)__runtime_v86_gdt; //[TODO: grab from vcpu]

		desc = (u64)(u32)__runtime_v86_tss; //[TODO: grab from vcpu]
		desc = ((desc & 0xFF000000)<<32)|((desc & 0x00FFFFFF)<<16);
		desc |= ( 8328 ) | (0x008BULL << 40);
		g_gdt[ V86M_SELECTOR_TASK >> 3 ] = desc;
			
		desc = (u64)(u32)__runtime_v86_ldt; //[TODO: grab from vcpu]
		desc = ((desc & 0xFF000000)<<32)|((desc & 0x00FFFFFF)<<16);
		desc |= ( 4 * 8 - 1) | (0x0082ULL << 40);
		g_gdt[ V86M_SELECTOR_LDTR >> 3 ] = desc;
	}

	//setup TSS
	{
		u32 *g_tss;
		memset((void *)__runtime_v86_tss, 0, 0x4000); //[TODO: grab from vcpu]
		g_tss = (u32 *)__runtime_v86_tss; //[TODO: grab from vcpu]
		g_tss[0] = 0;			// back-link
		g_tss[1] = (u32)__runtime_v86_ring0stack + 0x4000; // ESP0 [TODO: grab this from vcpu]
		g_tss[2] = V86M_SELECTOR_FLAT;	           // SS0
		g_tss[25] = 0x00880000;		// IOBITMAP offset
		// number of bytes in TSS: 104 + 32 + 8192 = 8328
		g_tss[ 8328 >> 2 ] = 0xFF;	// end of IOBITMAP
	}

  //setup guest registers
	vcpu->vmcs.guest_ES_selector = 0x0000;

	vcpu->vmcs.guest_CS_selector = 0x0000;
	vcpu->vmcs.guest_SS_selector = 0x6000;
	vcpu->vmcs.guest_DS_selector = 0x0000;
  vcpu->vmcs.guest_FS_selector = 0x0000;
	vcpu->vmcs.guest_GS_selector = 0x0000;
				
  /*      guest_RAX = 0;
				guest_RBX = 0;
				guest_RCX = 0;
				guest_RDX = 0;
				guest_RBP = 0;
				guest_RSI = 0;
				guest_RDI = 0;
  */
  

	vcpu->vmcs.guest_RSP = 0x4000;
	vcpu->vmcs.guest_RIP = 0x7c00;

	vcpu->vmcs.guest_RFLAGS = 0; 
	vcpu->vmcs.guest_RFLAGS &= ~((1<<3)|(1<<5)|(1<<15));	// reserved 0-bits
	vcpu->vmcs.guest_RFLAGS |= (1<<1);				// reserved 1-bits
	vcpu->vmcs.guest_RFLAGS |= (1<<17);			// Virtual-8086 = enable
	vcpu->vmcs.guest_RFLAGS |= (3<<12);			// IO-privilege-level = 3 
	vcpu->vmcs.guest_RFLAGS |= (1<<9);				// IF = enable 
	vcpu->vmcs.guest_RFLAGS &= ~(1<<14);			// Nested Task = disable
				
	vcpu->vmcs.guest_ES_base = (vcpu->vmcs.guest_ES_selector << 4);
	vcpu->vmcs.guest_CS_base = (vcpu->vmcs.guest_CS_selector << 4);
	vcpu->vmcs.guest_SS_base = (vcpu->vmcs.guest_SS_selector << 4);
	vcpu->vmcs.guest_DS_base = (vcpu->vmcs.guest_DS_selector << 4);
	vcpu->vmcs.guest_FS_base = (vcpu->vmcs.guest_FS_selector << 4);
	vcpu->vmcs.guest_GS_base = (vcpu->vmcs.guest_GS_selector << 4);
			
  vcpu->vmcs.guest_ES_limit = 0xFFFF;
	vcpu->vmcs.guest_CS_limit = 0xFFFF;
	vcpu->vmcs.guest_SS_limit = 0xFFFF;
	vcpu->vmcs.guest_DS_limit = 0xFFFF;
	vcpu->vmcs.guest_FS_limit = 0xFFFF;
	vcpu->vmcs.guest_GS_limit = 0xFFFF;
	vcpu->vmcs.guest_ES_access_rights = 0xF3;
	vcpu->vmcs.guest_CS_access_rights = 0xF3;
	vcpu->vmcs.guest_SS_access_rights = 0xF3;
	vcpu->vmcs.guest_DS_access_rights = 0xF3;
	vcpu->vmcs.guest_FS_access_rights = 0xF3;
	vcpu->vmcs.guest_GS_access_rights = 0xF3;
				
	vcpu->vmcs.guest_CR0 = vcpu->vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR];
	vcpu->vmcs.guest_CR4 = vcpu->vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR];
				
	vcpu->vmcs.guest_CR3 = __hva2spa__((u32)__runtime_v86_pagedir);
  vcpu->vmcs.guest_VMCS_link_pointer_full = (u32)0xFFFFFFFFUL;
	vcpu->vmcs.guest_VMCS_link_pointer_high = (u32)0xFFFFFFFFUL;
	vcpu->vmcs.guest_IDTR_base = (u32)__runtime_v86_idt;
	vcpu->vmcs.guest_GDTR_base = (u32)__runtime_v86_gdt;
	vcpu->vmcs.guest_LDTR_base = (u32)__runtime_v86_ldt;
	vcpu->vmcs.guest_TR_base   = (u32)__runtime_v86_tss;
	vcpu->vmcs.guest_IDTR_limit = (256 * 8) - 1;	// 256 descriptors
	vcpu->vmcs.guest_GDTR_limit = (3 * 8) - 1;		// 3 descriptors
	vcpu->vmcs.guest_LDTR_limit = (4 * 8) - 1;		// 4 descriptors
	vcpu->vmcs.guest_TR_limit   = (26 * 4) + 0x20 + 0x2000;
	vcpu->vmcs.guest_LDTR_access_rights = 0x82;
	vcpu->vmcs.guest_TR_access_rights   = 0x8B;
	vcpu->vmcs.guest_LDTR_selector = V86M_SELECTOR_LDTR;
	vcpu->vmcs.guest_TR_selector   = V86M_SELECTOR_TASK;
}
