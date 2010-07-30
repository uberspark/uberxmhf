//------------------------------------------------------------------------------
//v86monitor.c
//
// intel v8086 monitor to run real-mode code within v86 for Intel VT
// without support for "unrestricted guest" bit
//
// author: amit vasudevan (amitvasudevan@acm.org)

#include <types.h>
#include <target.h>
#include <print.h>
#include <processor.h>
#include <msr.h>
#include <vtx.h>
#include <paging.h>
#include <io.h>
#include <str.h>
#include <error.h>
#include <machine.h>

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
u32 v86monitor_guest_reg_cr0=__V86M_CR0_INITVAL; 

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
typedef struct {
	u32 baseaddrlow;
	u32 baseaddrhigh;
	u32 lengthlow;
	u32 lengthhigh;
	u32 type;
} __attribute__((packed)) E820ARD;

/*
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


//e820 map of HP Laptop (ADAMS)
E820ARD e820map[]={
	{0x00000000, 0x00000000, 0x0009fc00, 0x0, 0x1},
	{0x0009fc00, 0x00000000, 0x00000400, 0x0, 0x2},
	{0x000ef000, 0x00000000, 0x00020000, 0x0, 0x2},
//	{0x00100000, 0x00000000, 0xB8E43000, 0x0, 0x1},

//	{0x00100000, 0x00000000, 0x1FF00000, 0x0, 0x1},
//	{0x20000000, 0x00000000, 0x98F43000, 0x0, 0x2},

//	{0x00100000, 0x00000000, 0x3FF00000, 0x0, 0x1},
	//{0x40000000, 0x00000000, 0x78F43000, 0x0, 0x2},
	{0x00100000, 0x00000000, 0x7FF00000, 0x0, 0x1},
	{0x80000000, 0x00000000, 0x38F43000, 0x0, 0x2},


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


void handle_e820(INTRREGS *i, FAULTFRAME *f){

		if(i->edx != 'SMAP'){
				printf("\nunhandled INT15h E820, invalid signature!");
				HALTV86M();
		}			
			
		//return value, CF=0 indicated no error, EAX='SMAP'
		//ES:DI left untouched, ECX=size returned, EBX=next continuation value
		//EBX=0 if last descriptor
		if(i->ebx > (max_e820map_index-1)){
				printf("\ninvalid continuation value specified!");
				HALTV86M();				
		}
			
		//printf("\nECX=%u", i->ecx);
			
		//printf("\nreturning for index=%u", i->ebx);
		//printf("\nES=0x%04X, DI=0x%04X", (u16)f->es, (u16)i->edi);
		memcpy((void *)((f->es * 16)+(u16)i->edi), &e820map[i->ebx],
					sizeof(E820ARD));
		i->ebx=i->ebx+1;
				
				
		i->eax=i->edx;
		i->ecx=20;

		if(i->ebx > (max_e820map_index-1)){
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
		//printf("\nE820 request at CS:EIP=0x%04x:0x%08lx", 
		//	(u16)f->cs, f->eip);
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

