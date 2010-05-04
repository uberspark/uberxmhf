//------------------------------------------------------------------------------
// islayer_skeleton.c
//
// intel VT isolation layer. prepares guest execution state, launches/resumes 
// guest, handles intercepts and errors from guest
// 
// this is the skeleton implementation of the isolation layer which means it
// does not support hardware or shadow paging mechanisms. 
//
// author: amit vasudevan (amitvasudevan@acm.org)
//------------------------------------------------------------------------------

#include <types.h>
#include <target.h>
#include <print.h>
#include <processor.h>
#include <msr.h>
#include <vtx.h>
#include <paging.h>
#include <io.h>
#include <str.h>
#include <machine.h>
#include <error.h>
#include "acpi.h"
#include <disk.h>

u32 isl_guesthastr=0;

u32 isl_guest_TR_base   = 0;
u32 isl_guest_TR_access_rights   = 0;
u32 isl_guest_TR_limit   = 0;
u16 isl_guest_TR_selector=0;
u32 isl_guest_LDTR_base   = 0;
u32 isl_guest_LDTR_access_rights   = 0;
u32 isl_guest_LDTR_limit   = 0;
u16 isl_guest_LDTR_selector=0;

u32 limbo_rsp=0;

unsigned long long  efcr, efer;
u8	cpu_oem[ 16 ];
u32	cpu_features;
unsigned long long  msr0x480[ 12 ];
char *legend[] = {	"IA32_VMX_BASIC_MSR",		// 0x480
			"IA32_VMX_PINBASED_CTLS_MSR",	// 0x481
			"IA32_VMX_PROCBASED_CTLS_MSR",	// 0x482
			"IA32_VMX_EXIT_CTLS_MSR",	// 0x483
			"IA32_VMX_ENTRY_CTLS_MSR",	// 0x484
			"IA32_VMX_MISC_MSR",		// 0x485
			"IA32_VMX_CR0_FIXED0_MSR",	// 0x486
			"IA32_VMX_CR0_FIXED1_MSR",	// 0x487
			"IA32_VMX_CR4_FIXED0_MSR",	// 0x488
			"IA32_VMX_CR4_FIXED1_MSR",	// 0x489
			"IA32_VMX_VMCS_ENUM_MSR",	// 0x48A
			"IA32_VMX_PROCBASED_CTLS2_MSR",	// 0x48B
		};

u64  vmxon_region;
u64  guest_region;

u64  pgdir_region;
u64  pgtbl_region;
u64  iomap_region;
u64  g_IDT_region;
u64  g_GDT_region;
u64  g_LDT_region;
u64  g_TSS_region;
u64  g_SS0_region;
u64  g_ISR_region;
u64  h_MSR_region;

u32	guest_RAX, guest_RBX, guest_RCX, guest_RDX;
u32	guest_RBP, guest_RSI, guest_RDI;
u32 guest_CR2;


u32 retval;
unsigned long	msr_index, msr_value;
void		*next_host_MSR_entry;

#define VMXON_OFFSET	0x0000
#define GUEST_OFFSET	0x1000
#define PAGE_DIR_OFFSET	0x2000
#define PAGE_TBL_OFFSET 0x3000
#define IOBITMAP_OFFSET 0x4000
#define IDT_KERN_OFFSET 0x6000
#define GDT_KERN_OFFSET 0x6800
#define LDT_KERN_OFFSET 0x6A00
#define TSS_KERN_OFFSET 0x6C00
#define SS0_KERN_OFFSET 0xA000
#define ISR_KERN_OFFSET 0xA000
#define MSR_KERN_OFFSET	0xC000

#define __SELECTOR_TASK 0x0008
#define __SELECTOR_LDTR 0x0010
#define __SELECTOR_CODE 0x0004
#define __SELECTOR_DATA 0x000C
#define __SELECTOR_VRAM 0x0014
#define __SELECTOR_FLAT 0x001C

//------------------------------------------------------------------------------
// print guest state
void isl_printgueststate(void){
		printf("\nGuest State follows:");
		printf("\nguest_CS_selector=0x%04x", (unsigned short)guest_CS_selector);
		printf("\nguest_DS_selector=0x%04x", (unsigned short)guest_DS_selector);
		printf("\nguest_ES_selector=0x%04x", (unsigned short)guest_ES_selector);
		printf("\nguest_FS_selector=0x%04x", (unsigned short)guest_FS_selector);
		printf("\nguest_GS_selector=0x%04x", (unsigned short)guest_GS_selector);
		printf("\nguest_SS_selector=0x%04x", (unsigned short)guest_SS_selector);
		printf("\nguest_TR_selector=0x%04x", (unsigned short)guest_TR_selector);
		printf("\nguest_LDTR_selector=0x%04x", (unsigned short)guest_LDTR_selector);
		printf("\nguest_CS_access_rights=0x%08lx", 
			(unsigned long)guest_CS_access_rights);
		printf("\nguest_DS_access_rights=0x%08lx", 
			(unsigned long)guest_DS_access_rights);
		printf("\nguest_ES_access_rights=0x%08lx", 
			(unsigned long)guest_ES_access_rights);
		printf("\nguest_FS_access_rights=0x%08lx", 
			(unsigned long)guest_FS_access_rights);
		printf("\nguest_GS_access_rights=0x%08lx", 
			(unsigned long)guest_GS_access_rights);
		printf("\nguest_SS_access_rights=0x%08lx", 
			(unsigned long)guest_SS_access_rights);
		printf("\nguest_TR_access_rights=0x%08lx", 
			(unsigned long)guest_TR_access_rights);
		printf("\nguest_LDTR_access_rights=0x%08lx", 
			(unsigned long)guest_LDTR_access_rights);

		printf("\nguest_CS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)guest_CS_base, (unsigned short)guest_CS_limit);
		printf("\nguest_DS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)guest_DS_base, (unsigned short)guest_DS_limit);
		printf("\nguest_ES_base/limit=0x%08lx/0x%04x", 
			(unsigned long)guest_ES_base, (unsigned short)guest_ES_limit);
		printf("\nguest_FS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)guest_FS_base, (unsigned short)guest_FS_limit);
		printf("\nguest_GS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)guest_GS_base, (unsigned short)guest_GS_limit);
		printf("\nguest_SS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)guest_SS_base, (unsigned short)guest_SS_limit);
		printf("\nguest_GDTR_base/limit=0x%08lx/0x%04x",
			(unsigned long)guest_GDTR_base, (unsigned short)guest_GDTR_limit);		
		printf("\nguest_IDTR_base/limit=0x%08lx/0x%04x",
			(unsigned long)guest_IDTR_base, (unsigned short)guest_IDTR_limit);		
		printf("\nguest_TR_base/limit=0x%08lx/0x%04x",
			(unsigned long)guest_TR_base, (unsigned short)guest_TR_limit);		
		printf("\nguest_LDTR_base/limit=0x%08lx/0x%04x",
			(unsigned long)guest_LDTR_base, (unsigned short)guest_LDTR_limit);		

		printf("\nguest_CR0=0x%08lx, guest_CR4=0x%08lx, guest_CR3=0x%08lx",
			(unsigned long)guest_CR0, (unsigned long)guest_CR4,
			(unsigned long)guest_CR3);
		printf("\nguest_RSP=0x%08lx", (unsigned long)guest_RSP);
		printf("\nguest_RIP=0x%08lx", (unsigned long)guest_RIP);
		printf("\nguest_RFLAGS=0x%08lx", (unsigned long)guest_RFLAGS);
}
//------------------------------------------------------------------------------


void isl_handleintercept_cpuid(void){
	//printf("\n0x%04x:%08lx : CPUID(EAX=0x%08lx/ECX=0x%08lx)", 
	//	(unsigned short)guest_CS_selector, (unsigned long)guest_RIP,
	//	(unsigned long)guest_RAX, (unsigned long)guest_RCX);
	asm volatile ("cpuid\r\n"
          :"=a"(guest_RAX), "=b"(guest_RBX), "=c"(guest_RCX), "=d"(guest_RDX)
          :"a"(guest_RAX), "c" (guest_RCX));
	//printf(" --> EAX/EBX/ECX/EDX=0x%08lx/0x%08lx/0x%08lx/0x%08lx", 
	//		(unsigned long)guest_RAX, 
	//		(unsigned long)guest_RBX, 
	//		(unsigned long)guest_RCX, 
	//		(unsigned long)guest_RDX);
	
	guest_RIP +=info_vmexit_instruction_length;
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

void isl_handleintercept_wrmsr(void){
	//printf("\n%s: ECX=0x%08lx, EDX:EAX=0x%08lx:0x%08lx", __FUNCTION__, 
	//	(unsigned long)guest_RCX, 
	//	(unsigned long)guest_RDX, (unsigned long)guest_RAX);
	
	switch(guest_RCX){
		case IA32_SYSENTER_CS:
			guest_SYSENTER_CS = (unsigned int)guest_RAX;
			//printf("\nWRMSR(IA32_SYSENTER_CS) = 0x%08lx", (unsigned long)guest_SYSENTER_CS);
			break;
		case IA32_SYSENTER_EIP:
			guest_SYSENTER_EIP = (unsigned long long)guest_RAX;
			//printf("\nWRMSR(IA32_SYSENTER_EIP) = 0x%08lx", (unsigned long)guest_SYSENTER_EIP);
			break;
		case IA32_SYSENTER_ESP:
			guest_SYSENTER_ESP = (unsigned long long)guest_RAX;
			//printf("\nWRMSR(IA32_SYSENTER_ESP) = 0x%08lx", (unsigned long)guest_SYSENTER_ESP);
			break;
		default:{
			asm volatile ("wrmsr\r\n"
          : //no outputs
          :"a"(guest_RAX), "c" (guest_RCX), "d" (guest_RDX));	
			break;
		}
	}
	
	
	guest_RIP +=info_vmexit_instruction_length;
}

void isl_handleintercept_rdmsr(void){
	//printf("\n%s: ECX=0x%08lx", __FUNCTION__, 
	//	(unsigned long)guest_RCX);

	switch(guest_RCX){
		case IA32_SYSENTER_CS:
			guest_RAX = (u32)guest_SYSENTER_CS;
			guest_RDX = 0;
			//printf("\nRDMSR(IA32_SYSENTER_CS)= 0x%08lx", (unsigned long)guest_SYSENTER_CS);
			break;
		case IA32_SYSENTER_EIP:
			guest_RAX = (u32)guest_SYSENTER_EIP;
			guest_RDX = 0;
			//printf("\nRDMSR(IA32_SYSENTER_EIP)= 0x%08lx", (unsigned long)guest_SYSENTER_EIP);
			break;
		case IA32_SYSENTER_ESP:
			guest_RAX = (u32)guest_SYSENTER_ESP;
			guest_RDX = 0;
			//printf("\nRDMSR(IA32_SYSENTER_ESP)= 0x%08lx", (unsigned long)guest_SYSENTER_ESP);
			break;
		default:{
			asm volatile ("rdmsr\r\n"
          : "=a"(guest_RAX), "=d"(guest_RDX)
          : "c" (guest_RCX));
			break;
		}
	
	}
	
	//printf("\n%s: EDX:EAX=0x%08lx:0x%08lx", __FUNCTION__, 
	//	(unsigned long)guest_RDX, (unsigned long)guest_RAX);
	
	guest_RIP +=info_vmexit_instruction_length;
}
//------------------------------------------------------------------------------



void isl_handleintercept_hlt(void){
	//we should be called when the v86monitor causes a world switch
	//to end real-mode execution
	//sanity check guest state, cr0 contents and gdt
	if( !((guest_currentstate == GSTATE_REALMODE) && 
			(v86monitor_guest_reg_cr0 & CR0_PE) &&
			(v86monitor_guest_gdt_base != 0) &&
			(v86monitor_guest_gdt_limit != 0) ) ){
		printf("\nIntercept(HLT): undefined guest condition!");
		HALT();
	}

	printf("\nIntercept(HLT): Guest going to protected mode (CR0=0x%08x)...",
		v86monitor_guest_reg_cr0);
					
	
	guest_nextstate = GSTATE_PROTECTEDMODE;
				
	if(v86monitor_guest_reg_cr0 & CR0_PG)
		guest_nextstate |= GSTATE_PROTECTEDMODE_PG;
	
	control_CR0_shadow = v86monitor_guest_reg_cr0;
		
	guest_currentstate = isl_prepareVMCS(guest_currentstate, guest_nextstate);
}

u16 guest_limbo_cs=0;
//u16 guest_limbo_ip=0;
u32 guest_limbo_eip=0;

void isl_handleintercept_exception_0D(u32 errorcode){
	u32 pcpaddr, stackpaddr;
	(void)errorcode;
	ASSERT( (guest_currentstate == GSTATE_PROTECTEDMODE) ||
				(guest_currentstate == (GSTATE_PROTECTEDMODE | GSTATE_PROTECTEDMODE_PG)) 
				);
	
	//printf("\nIntercept(EXCP-0D): End of protected mode limbo");
	//printf("\nerrorcode=0x%08lx", (unsigned long)errorcode);
	//printf("\nguest_RSP=0x%08lx", (unsigned long)guest_RSP);
	//printf("\nguest_SS_base=0x%08lx", (unsigned long)guest_SS_base);
	//printf("\nguest_RIP=0x%08lx", (unsigned long)guest_RIP);
	//printf("\nguest_CS_base=0x%08lx", (unsigned long)guest_CS_base);
	
	pcpaddr = guest_CS_base + guest_RIP;
	if(*((u8 *)pcpaddr) == 0xCB){
		//retf
		stackpaddr = guest_SS_base + (u16)guest_RSP;
		guest_limbo_eip =  (u32)(*(u16 *)stackpaddr);
		guest_limbo_cs = *(u16 *)((u32)stackpaddr+2);
		//printf("\nretf: guest_limbo cs:ip=0x%04x:0x%04x", guest_limbo_cs,
		//		(u16)guest_limbo_eip);
		guest_RSP += 4;
	}else if(*((u8 *)pcpaddr) == 0xEA){
 		//jmp sel:off 16-bit off
		guest_limbo_eip = (u32)(*(u16 *)((u32)pcpaddr+1));
		guest_limbo_cs = *(u16 *)((u32)pcpaddr+3);
		//printf("\n(jmp16-bit)INT 0D: target CS:EIP=0x%04x:0x%08x",
		//	guest_limbo_cs, guest_limbo_eip);
		guest_RIP += 5; 		
	}else if(*((u8 *)pcpaddr) == 0x66 && *((u8 *)pcpaddr+1) == 0xEA){
 		//jmp sel:off 32-bit off
		guest_limbo_eip = *(u32 *)((u32)pcpaddr+2);
		guest_limbo_cs = *(u16 *)((u32)pcpaddr+6);
		//printf("\n(jmp-32-bit:INT 0D: target CS:EIP=0x%04x:0x%08x (32-bit)",
		//	guest_limbo_cs, guest_limbo_eip);
		guest_RIP += 8; 		
	}else{
		printf("\n%s: unrecognized opcode, dump follows...\n", __FUNCTION__);
		{
			u8 *ch=(u8 *)pcpaddr;
			int i;
			for(i=0; i < 16; i++)
				printf("%02x ", ch[i]);
			printf("\nHalt!");
		}
		HALT();
	}

	/*printf("\nDump follows:\n");
	{
			u8 *ch=(u8 *)pcpaddr;
			int i;
			for(i=0; i < 16; i++)
				printf("%02x ", ch[i]);
			printf("\nDone dumping");
	}*/


	guest_nextstate = guest_currentstate | GSTATE_PROTECTEDMODE_GDTR;
	if( (v86monitor_guest_idt_base != 0) || 
			(v86monitor_guest_idt_limit != 0) )
			guest_nextstate |= GSTATE_PROTECTEDMODE_IDTR;
			
	//printf("\ngoing from state=0x%08lx tp 0x%08lx", 
	//	(unsigned long)guest_currentstate,
	//	(unsigned long)guest_nextstate);
	guest_currentstate = isl_prepareVMCS(guest_currentstate, guest_nextstate);
	
}

//------------------------------------------------------------------------------
u32 islgprtable[] = { (u32)&guest_RAX,	(u32)&guest_RCX,	(u32)&guest_RDX,	
											(u32)&guest_RBX,	(u32)&guest_RSP,	(u32)&guest_RBP,	
											(u32)&guest_RSI,	(u32)&guest_RDI };

u32 guestcr3val_when_cr0_pg_off=0; //contains CR3 values manipulated by guest when CR0.PG=0

//we get here only if any of the bits specified by 
//control_cr0_mask get modified. This includes 
//CR0.PG, CR0.PE, CR0.NE, CR0.ET and CR0.WP 
void handle_intercept_cr0access(u32 gpr, u32 tofrom){
	u32 cr0value;
	//printf("\n%s: gpr=%u, tofrom=%u", __FUNCTION__, gpr, tofrom);
	
	ASSERT(tofrom == VMX_CRX_ACCESS_TO);
	ASSERT( (guest_currentstate & GSTATE_PROTECTEDMODE) &&
		(guest_currentstate & (GSTATE_PROTECTEDMODE | GSTATE_PROTECTEDMODE_GDTR)) );
	
	cr0value = *((u32 *)islgprtable[gpr]);
	
	//we handle two situations, CR0_PG being turned on and off while in PMODE
	//PMODE itself turned off (as a result CR0_PG must be turned off)
	if( (cr0value & CR0_PE) && 
			(control_CR0_shadow & CR0_PG) && !(cr0value & CR0_PG)){
		//printf("\n0x%04x:0x%08lx -> CR0.PG=0 (paging disabled)", (unsigned short)guest_CS_selector, (unsigned long)guest_RIP);
		//printf("\nCR3=0x%08lx, CR4=0x%08lx", (unsigned long)guest_CR3, (unsigned long)guest_CR4);

		guestcr3val_when_cr0_pg_off = guest_CR3;
		
		guest_CR3 = (u32)__runtime_v86_pagedir;	//load our unity mapping
		guest_CR4 &= ~(CR4_PAE);	//disable CR4_PAE if enabled
		
		control_CR0_shadow &= ~(CR0_PG);

		control_VMX_cpu_based |= (1 << 15); //enable CR3 load exiting
		control_VMX_cpu_based |= (1 << 16); //enable CR3 store exiting
					
		guest_currentstate &= ~(GSTATE_PROTECTEDMODE_PG);
		return;
	}else if 
		((cr0value & CR0_PE) && 
		!(control_CR0_shadow & CR0_PG) && (cr0value & CR0_PG)){
		//printf("\n0x%04x:0x%08lx -> CR0.PG=1 (paging enabled)",
		//	(unsigned short)guest_CS_selector, (unsigned long)guest_RIP);
		
		control_CR0_shadow |= CR0_PG;

		//if CR4.PAE was manipulated in real-mode, control_CR4_shadow would have
		//the correct PAE bit, so propagate it to CR4 since we had disabled PAE
		//for our unity mapping
		if(control_CR4_shadow & CR4_PAE){
			//printf("\nEnabling PAE");
			guest_CR4 |= CR4_PAE;
		}
		guest_CR3 = guestcr3val_when_cr0_pg_off;

		//control_VMX_cpu_based &= ~(1 << 15); //disable CR3 load exiting
		//control_VMX_cpu_based &= ~(1 << 16); //disable CR3 store exiting

		

		guest_currentstate |= (GSTATE_PROTECTEDMODE_PG);
		return;		
	}else if (!(cr0value & CR0_PE)){
		ASSERT(!(cr0value & CR0_PG)); //CR0_PG must be set to 0 if going to real 
		//printf("\nguest is going to real-mode...");
		guest_nextstate = GSTATE_REALMODE;
		guest_CR0 = v86monitor_guest_reg_cr0 = cr0value;
		//guest_CR0 |= CR0_WP;
		control_CR0_shadow &= ~(CR0_PG);
		control_CR0_shadow &= ~(CR0_PE);
		guest_currentstate = isl_prepareVMCS(guest_currentstate, guest_nextstate);
		return;
	}
	
	//printf("\nUnhandled transition of CR0: curr=0x%08lx, next=0x%08lx, mask=0x%08lx, shadow=0x%08lx",
	//			(unsigned long)guest_CR0, (unsigned long)cr0value,
	//				(unsigned long)control_CR0_mask, (unsigned long)control_CR0_shadow);
	//HALT();
}


void handle_intercept_cr3access(u32 gpr, u32 tofrom){
	//printf("\n0x%04x:0x%08x: CR3 access gpr=%u, tofrom=%u", (unsigned short)guest_CS_selector,
	//(unsigned int)guest_RIP, gpr, tofrom);
	
	if(control_CR0_shadow & CR0_PG){

		if(tofrom == VMX_CRX_ACCESS_FROM){
			*((u32 *)islgprtable[gpr]) = guest_CR3;
		}else{
			guest_CR3 = *((u32 *)islgprtable[gpr]);		
		}
	}else{
		//CR3 read/write when CR0.PG is off, blah, we will handle this
		//when CR0.PG is set again
		//printf("\nCR0.PG=0, read/write to guestcr3val");
		if(tofrom == VMX_CRX_ACCESS_FROM)
			*((u32 *)islgprtable[gpr]) = guestcr3val_when_cr0_pg_off;
		else
			guestcr3val_when_cr0_pg_off = *((u32 *)islgprtable[gpr]);		
	}
		
}

void handle_intercept_cr4access(u32 gpr, u32 tofrom){
	//printf("\n0x%04x:0x%08x: CR4 access gpr=%u, tofrom=%u", (unsigned short)guest_CS_selector,
	//(unsigned int)guest_RIP, gpr, tofrom);
	
	ASSERT(tofrom == VMX_CRX_ACCESS_TO);
	
	//ASSERT( ( (*((u32 *)islgprtable[gpr]) & CR4_PAE) && !(control_CR4_shadow & CR4_PAE) ) ||
	//	( !(*((u32 *)islgprtable[gpr]) & CR4_PAE) && (control_CR4_shadow & CR4_PAE) )	); 
	//note: the above assertion is incorrect since there can be a mov to CR4
	//to flush TLB, linux is guilty of this
	
	
	if ( (*((u32 *)islgprtable[gpr]) & CR4_PAE) && !(control_CR4_shadow & CR4_PAE) ){
		//PAE being enabled by guest
		printf("\nPAE enabled by guest.");
		control_CR4_shadow |= CR4_PAE;
	}else if ( !(*((u32 *)islgprtable[gpr]) & CR4_PAE) && (control_CR4_shadow & CR4_PAE) ) {
		//PAE being disabled by guest
		printf("\nPAE disabled by guest.");
		control_CR4_shadow &= ~CR4_PAE;
	} else {
		printf("\nMOV TO CR4 (flush TLB?), current=0x%08x, proposed=0x%08x",
			(u32)guest_CR4, *((u32 *)islgprtable[gpr]) );
	}

	//check if we are operating in protected mode with paging, if so
	//simply propagate the value of CR4 to guest
	//if( (guest_currentstate & GSTATE_PROTECTEDMODE) &&
	//			(guest_currentstate & GSTATE_PROTECTEDMODE_PG) ){
	//		printf("\nGuest is in protected mode with paging, simply propagate CR4");	
	//		guest_CR4 = *((u32 *)islgprtable[gpr]);
	//		guest_CR4 |= msr0x480[8];
	//}else{


		//ok, if CR0.PG is off we dont update CR4 now, else blasted VMX
		//will go into an abort especially with M$ coders not adhering to
		//VMX standards or should we say Intel forgot that they had to be
		//backward compatible with the following code from ntldr????...DOH!!!
		//.text:00430DF3                 mov     edx, [esp+arg_0]
		//.text:00430DF7                 mov     ecx, cr3
		//.text:00430DFA                 mov     cr3, ecx
		//.text:00430DFD                 mov     eax, cr0
		//.text:00430E00                 and     eax, 7FFFFFFFh
		//.text:00430E05                 mov     cr0, eax
		//.text:00430E08                 jmp     short $+2
		//.text:00430E0A                 mov     eax, cr4
		//.text:00430E0D                 or      eax, 20h
		//.text:00430E10                 mov     ecx, cr3
		//.text:00430E13                 mov     cr4, eax ;<--- CR4 PAE set BEFORE CR3 loaded with valid PDPT 
		//.text:00430E16                 mov     cr3, edx ;     VMX checks PDPT on CR4 load, but HEY its not valid, so ABORT!!!
		//.text:00430E19                 mov     ecx, cr0
		//.text:00430E1C                 or      ecx, 80000000h
		//.text:00430E22                 mov     cr0, ecx
		//.text:00430E25                 jmp     short $+2
		//.text:00430E27                 retn    4
			
	
		if(control_CR0_shadow & CR0_PG){
			//printf("\nGuest has Paging enabled, so enable CR4 immediately");
			guest_CR4 = *((u32 *)islgprtable[gpr]);
			guest_CR4 |= msr0x480[8];
	
			//check guest PDPTEs, wee need to inject GPF if not valid, TODO
			{
				int i;
				u64 pdpte;
				unsigned offset = (guest_CR3 & (4096-1)) >> 5;
				u64 *pdpt = (u64 *) (u32)guest_CR3;
	
				for (i = 0; i < 4; ++i) {
					pdpte = pdpt[offset + i];
					if ((pdpte & 1) && (pdpte & 0xfffffff0000001e6ull))
						break;
				}
	
				if (i != 4) {
					printf("%s: pae cr3[%d] 0x%llx, reserved bits\n",
						   __FUNCTION__, i, pdpte);
					HALT();
				}
			}
		}
	//}
	
}


//------------------------------------------------------------------------------
// VMX generic event injection function
// injects: software interrupts, hardware interrupts, exceptions
// if any of them need to be injected back to the guest
static void vmx_inject_event(u32 idt_vectoring_information, u32 idt_vectoring_error_code){
	u32 vector, type;
	
	if( !(idt_vectoring_information & VECTORING_INFO_VALID_MASK) )
		return;	 //no events to inject
		
	vector = idt_vectoring_information & VECTORING_INFO_VECTOR_MASK;
	type = (idt_vectoring_information & VECTORING_INFO_TYPE_MASK);
	
	if( !( (type == INTR_TYPE_HW_INTERRUPT) || (type == INTR_TYPE_HW_EXCEPTION) ||
					(type == INTR_TYPE_SW_INTERRUPT) || (type == INTR_TYPE_SW_EXCEPTION) ) ){
		printf("\n%s: Unhandled vectoring type=%u, vector=%u", __FUNCTION__, type, vector);
		HALT();
	}

	//check if guest is in a state to inject this event
	if(type == INTR_TYPE_HW_INTERRUPT || type == INTR_TYPE_SW_INTERRUPT){
		u32 interrupt_window_open;
		
		interrupt_window_open = (guest_RFLAGS & EFLAGS_IF) && 
			((guest_interruptibility & 3) == 0);
			
		if(interrupt_window_open && 
			!(control_VM_entry_interruption_information & INTR_INFO_VALID_MASK)){
			//printf("\nInject OK");			
		}else{
			printf("\nHAHA moron, you werent supposed to inject now!!!!");
				HALT();
		}
	
	}
						
  control_VM_entry_interruption_information = vector | type | INTR_INFO_VALID_MASK; 					
					
	if(idt_vectoring_information & VECTORING_INFO_DELIVER_CODE_MASK){
		control_VM_entry_exception_errorcode = idt_vectoring_error_code;
		control_VM_entry_interruption_information |= INTR_INFO_DELIVER_CODE_MASK; 
	}else{
		control_VM_entry_exception_errorcode = 0;
	}  

	//
	if (type == INTR_TYPE_SW_INTERRUPT || type == INTR_TYPE_SW_EXCEPTION)
		control_VM_entry_instruction_length = info_vmexit_instruction_length;

	//printf("\n%s: type=%u, vector=%u, e=0x%08x (%u)", __FUNCTION__,
	//	(type >> 8), vector, control_VM_entry_exception_errorcode, 
	//	(control_VM_entry_interruption_information & INTR_INFO_DELIVER_CODE_MASK) );
}
//------------------------------------------------------------------------------


void isl_handle_intercept_ioportaccess(u32 portnum, u32 access_type, u32 access_size, u32 stringio){
	//printf("\n0x%04x:0x%08lx -> IO: port=0x%04x, type=%u, size=%u",
	//	(u16)guest_CS_selector, (u32)guest_RIP, 
	//	(u16)portnum, access_type, access_size);
	ASSERT(!stringio);	//we dont handle string IO intercepts
	
	if(access_type == IO_TYPE_OUT){
		//printf(" --> EAX=0x%08lx", guest_RAX);
		if(portnum == ACPI_CONTROLREG_PORT && access_size == IO_SIZE_WORD){
			if( (u16)guest_RAX & (u16)(1 << 13) ){
				printf("\nACPI Sleep_EN toggled, hibernation caught..resetting...");
				/*if(!DiskSetIndicator(1, __LDN_MODE_UNTRUSTED)){
					printf("\nerror setting operating mode!");
					HALT();
				}*/
				
				//sleep enable toggled, we just reset
				islayer_reboot();
			}
		}
		
		
		if( access_size== IO_SIZE_BYTE)
				outb(portnum, (u8)guest_RAX);
		else if (access_size == IO_SIZE_WORD)
				outw(portnum, (u16)guest_RAX);
		else if (access_size == IO_SIZE_DWORD)
				outl(portnum, (u32)guest_RAX);	

	}else{

		if( access_size== IO_SIZE_BYTE){
				guest_RAX &= 0xFFFFFF00UL;	//clear lower 8 bits
				guest_RAX |= (u8)inb(portnum);
		}else if (access_size == IO_SIZE_WORD){
				guest_RAX &= 0xFFFF0000UL;	//clear lower 16 bits
				guest_RAX |= (u16)inw(portnum);
		}else if (access_size == IO_SIZE_DWORD){
				guest_RAX = (u32)inl(portnum);	
		}

		//printf(" <-- EAX=0x%08lx", guest_RAX);
	}
	
	guest_RIP +=info_vmexit_instruction_length;

	return;
}




void vt_intercepthandler(void){


	if(info_vmexit_reason & 0x80000000){
		printf("\nVM-ENTRY error: reason=0x%08x, qualification=0x%016llx", 
			info_vmexit_reason, info_exit_qualification);
		printf("\nGuest State follows:");
		printf("\nguest_CS_selector=0x%04x", (unsigned short)guest_CS_selector);
		printf("\nguest_DS_selector=0x%04x", (unsigned short)guest_DS_selector);
		printf("\nguest_ES_selector=0x%04x", (unsigned short)guest_ES_selector);
		printf("\nguest_FS_selector=0x%04x", (unsigned short)guest_FS_selector);
		printf("\nguest_GS_selector=0x%04x", (unsigned short)guest_GS_selector);
		printf("\nguest_SS_selector=0x%04x", (unsigned short)guest_SS_selector);
		printf("\nguest_TR_selector=0x%04x", (unsigned short)guest_TR_selector);
		printf("\nguest_LDTR_selector=0x%04x", (unsigned short)guest_LDTR_selector);
		printf("\nguest_CS_access_rights=0x%08lx", 
			(unsigned long)guest_CS_access_rights);
		printf("\nguest_DS_access_rights=0x%08lx", 
			(unsigned long)guest_DS_access_rights);
		printf("\nguest_ES_access_rights=0x%08lx", 
			(unsigned long)guest_ES_access_rights);
		printf("\nguest_FS_access_rights=0x%08lx", 
			(unsigned long)guest_FS_access_rights);
		printf("\nguest_GS_access_rights=0x%08lx", 
			(unsigned long)guest_GS_access_rights);
		printf("\nguest_SS_access_rights=0x%08lx", 
			(unsigned long)guest_SS_access_rights);
		printf("\nguest_TR_access_rights=0x%08lx", 
			(unsigned long)guest_TR_access_rights);
		printf("\nguest_LDTR_access_rights=0x%08lx", 
			(unsigned long)guest_LDTR_access_rights);

		printf("\nguest_CS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)guest_CS_base, (unsigned short)guest_CS_limit);
		printf("\nguest_DS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)guest_DS_base, (unsigned short)guest_DS_limit);
		printf("\nguest_ES_base/limit=0x%08lx/0x%04x", 
			(unsigned long)guest_ES_base, (unsigned short)guest_ES_limit);
		printf("\nguest_FS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)guest_FS_base, (unsigned short)guest_FS_limit);
		printf("\nguest_GS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)guest_GS_base, (unsigned short)guest_GS_limit);
		printf("\nguest_SS_base/limit=0x%08lx/0x%04x", 
			(unsigned long)guest_SS_base, (unsigned short)guest_SS_limit);
		printf("\nguest_GDTR_base/limit=0x%08lx/0x%04x",
			(unsigned long)guest_GDTR_base, (unsigned short)guest_GDTR_limit);		
		printf("\nguest_IDTR_base/limit=0x%08lx/0x%04x",
			(unsigned long)guest_IDTR_base, (unsigned short)guest_IDTR_limit);		
		printf("\nguest_TR_base/limit=0x%08lx/0x%04x",
			(unsigned long)guest_TR_base, (unsigned short)guest_TR_limit);		
		printf("\nguest_LDTR_base/limit=0x%08lx/0x%04x",
			(unsigned long)guest_LDTR_base, (unsigned short)guest_LDTR_limit);		

		printf("\nguest_CR0=0x%08lx, guest_CR4=0x%08lx, guest_CR3=0x%08lx",
			(unsigned long)guest_CR0, (unsigned long)guest_CR4,
			(unsigned long)guest_CR3);
		printf("\nguest_RSP=0x%08lx", (unsigned long)guest_RSP);
		printf("\nguest_RIP=0x%08lx", (unsigned long)guest_RIP);
		printf("\nguest_RFLAGS=0x%08lx", (unsigned long)guest_RFLAGS);
		
		
		
		HALT();	//halt!
	}
	
	//printf("\nVM-EXIT: Exit Reason:0x%08x, Exit Qualification:0x%016llx",
	//	info_vmexit_reason, info_exit_qualification);
	//printf("\nGuest CS:EIP=0x%04x:0x%08lx", (unsigned short)guest_CS_selector,
	//	(unsigned long)guest_RIP);

	switch(info_vmexit_reason){
		case VMEXIT_IOIO:
			{
				u32 access_size, access_type, portnum, stringio;
				access_size = (u32)info_exit_qualification & 0x00000007UL;
				access_type = ((u32)info_exit_qualification & 0x00000008UL) >> 3;
				portnum =  ((u32)info_exit_qualification & 0xFFFF000UL) >> 16;
				stringio = ((u32)info_exit_qualification & 0x00000010UL) >> 4;
				isl_handle_intercept_ioportaccess(portnum, access_type, access_size, stringio);
			}
			break;
			
			
		case VMEXIT_RDMSR:
			isl_handleintercept_rdmsr();
			break;
			
		case VMEXIT_WRMSR:
			isl_handleintercept_wrmsr();
			break;
			
		case VMEXIT_CPUID:
			isl_handleintercept_cpuid();
			break;
		
		case VMEXIT_HLT:
			isl_handleintercept_hlt();
			break;
			
		case VMEXIT_CRX_ACCESS:{
			u32 tofrom, gpr, crx; 
			//printf("\nVMEXIT_CRX_ACCESS:");
			//printf("\ninstruction length: %u", info_vmexit_instruction_length);
			crx=(u32) ((u64)info_exit_qualification & 0x000000000000000FULL);
			gpr=
			 (u32) (((u64)info_exit_qualification & 0x0000000000000F00ULL) >> (u64)8);
			tofrom = 
			(u32) (((u64)info_exit_qualification & 0x0000000000000030ULL) >> (u64)4); 
			//printf("\ncrx=%u, gpr=%u, tofrom=%u", crx, gpr, tofrom);
			switch(crx){
				case 0x3: //CR3 access
					handle_intercept_cr3access(gpr, tofrom);
					break;
				
				case 0x4: //CR4 access
					handle_intercept_cr4access(gpr, tofrom);
					break;
				
				case 0x0: //CR0 access
					handle_intercept_cr0access(gpr, tofrom);
					break;
			
				default:
					printf("\nunhandled crx, halting!");
					HALT();
			}
			guest_RIP +=info_vmexit_instruction_length;
		}
		break;	
		
		case VMEXIT_EXCEPTION:{
			switch( ((u32)info_vmexit_interrupt_information & INTR_INFO_VECTOR_MASK) ){
				case 0x0D:
					isl_handleintercept_exception_0D(
							(u32)info_vmexit_interrupt_error_code);
					break;
				
				
				default:
					printf("\nVMEXIT-EXCEPTION:");
					printf("\ncontrol_exception_bitmap=0x%08lx",
						(unsigned long)control_exception_bitmap);
					printf("\ninterruption information=0x%08lx", 
						(unsigned long)info_vmexit_interrupt_information);
					printf("\nerrorcode=0x%08lx", 
						(unsigned long)info_vmexit_interrupt_error_code);
					HALT();
			}
		}
		break;

	  case 0x3:{	//INIT/reboot
			printf("\nINIT reboot signal received. rebooting");
			islayer_reboot();
			printf("\nnever comehere");
			HALT();		
		}
	  break;

		default:
			printf("\nunhandled intercept, halting!");
			printf("\nExit Reason:0x%08x, Exit Qualification:0x%016llx",
				info_vmexit_reason, info_exit_qualification);
			printf("\nGuest CS:EIP=0x%04x:0x%08lx", (unsigned short)guest_CS_selector,
				(unsigned long)guest_RIP);
			printf("\nGuest RFLAGS=0x%016x", guest_RFLAGS);
			if( ((u32)guest_RFLAGS & EFLAGS_IF) )
				printf("\nInterrupts enabled!!!");
			printf("\nIDT vectoring information=0x%08x", info_IDT_vectoring_information);
			HALT();	
	}


	//check guest interruptibility state
	if(guest_interruptibility != 0){
		printf("\nWARNING!: interruptibility=%08lx", (unsigned long)guest_interruptibility);
		guest_interruptibility = 0;
	}

	if(info_IDT_vectoring_information & 0x80000000){
				printf("\nHALT: Nested events unhandled when hardware paging in effect:0x%08X",
					info_IDT_vectoring_information);
				HALT();
	}

}

void vt_handleerror(void){
	printf("\nVT Instruction ERROR: 0x%08x", 
		info_vminstr_error);
	HALT();
}	

//------------------------------------------------------------------------------
// check for VT support and initialize 
// returns 1 on success, else 0
u32 runtime_initVT(void){
	retval=0;

	// verify cpu support for Intel Virtualization Technology
	asm(	"xor	%%eax, %%eax \n"
				"cpuid \n"		
				"mov	%%ebx, cpu_oem+0 \n"
				"mov	%%edx, cpu_oem+4 \n"
				"mov	%%ecx, cpu_oem+8 \n"
			::: "eax", "ebx", "ecx", "edx" );
	printf("\nCPU is: %s", cpu_oem );

	if ( strncmp( cpu_oem, (u8 *)"GenuineIntel", 12 ) == 0 ){
		asm("mov	$1, %%eax \n"
				"cpuid \n"
				"mov	%%ecx, cpu_features	\n"
				::: "eax", "ebx", "ecx", "edx" );
		if ( ( cpu_features & (1<<5) ) == 0 ){
			printf("VT unsupported!");
			return 0;
		}
	}else{
		printf("\nNon-Intel CPU. Unsupported!");
		return 0;
	}

	printf("\nCPU support VT. Reading VMX capabilities MSRS...");

	asm("xor	%%ebx, %%ebx \n"
			"mov	%0, %%ecx \n"
			"nxcap: \n"
			"rdmsr \n"
			"mov	%%eax, msr0x480+0(, %%ebx, 8 ) \n"
			"mov	%%edx, msr0x480+4(, %%ebx, 8 ) \n"
			"inc	%%ecx \n"
			"inc	%%ebx \n"
			"cmp	$11, %%ebx \n"
			"jb	nxcap \n"
			:: "i" (IA32_VMX_BASIC) : "eax", "ebx", "ecx", "edx" );

	{
		u32 i;
		printf("\nVMX capability MSRs:");
		for(i=0; i < 11; i++)
			printf("\n%s = %016llx", legend[i], msr0x480[i]);
	}

	printf("\nSaving MSR_EFCR and MSR_EFER...");
	// preserve original contents of Extended Feature Control Register
	asm(	" mov	%0, %%ecx			\n"\
		" rdmsr					\n"\
		" mov	%%eax, efcr+0			\n"\
		" mov	%%edx, efcr+4			\n"\
		:: "i" (MSR_EFCR) : "eax", "ecx", "edx" );

	// preserve original contents of Extended Feature Enable Register
	asm(	" mov	%0, %%ecx			\n"\
		" rdmsr					\n"\
		" mov	%%eax, efer+0			\n"\
		" mov	%%edx, efer+4			\n"\
		:: "i" (MSR_EFER) : "eax", "ecx", "edx" );
	printf("Done.");
		
	vmxon_region = (u64)(u32)__runtime_reachregion + VMXON_OFFSET;	
	guest_region = (u64)(u32)__runtime_reachregion + GUEST_OFFSET;	
	pgdir_region = (u64)(u32)__runtime_reachregion + PAGE_DIR_OFFSET;	
	pgtbl_region = (u64)(u32)__runtime_reachregion + PAGE_TBL_OFFSET;	
	iomap_region = (u64)(u32)__runtime_reachregion + IOBITMAP_OFFSET;	
	g_IDT_region = (u64)(u32)__runtime_reachregion + IDT_KERN_OFFSET;
	g_GDT_region = (u64)(u32)__runtime_reachregion + GDT_KERN_OFFSET;
	g_LDT_region = (u64)(u32)__runtime_reachregion + LDT_KERN_OFFSET;
	g_TSS_region = (u64)(u32)__runtime_reachregion + TSS_KERN_OFFSET;
	g_SS0_region = (u64)(u32)__runtime_reachregion + SS0_KERN_OFFSET;
	g_ISR_region = (u64)(u32)__runtime_reachregion + ISR_KERN_OFFSET;
	h_MSR_region = (u64)(u32)__runtime_reachregion + MSR_KERN_OFFSET;

	printf("\nEnabling VMX and entering VMX root...");
	//enable VMX by setting CR4 and enter VMX root operation using VMXON
	asm(	" mov  %%cr4, %%eax	\n"\
		" bts  $13, %%eax	\n"\
		" mov  %%eax, %%cr4	" ::: "eax" );

	//clear VMXON region and set VMCS revision identifier
	memset( (void *)(u32)vmxon_region, 0, 0x1000);
	memcpy( (void *)(u32)vmxon_region, msr0x480, 4);

	asm( "vmxon vmxon_region \n"
			 "jbe vmfail \n"
			 "movl $0x1, %%eax \n" 
			 "movl %%eax, retval \n"
			 "jmp vmsuccess \n"
			 "vmfail: \n"
			 "movl $0x0, %%eax \n"
			 "movl %%eax, retval \n"
			 "vmsuccess: \n" ::: "eax");
	
	printf("Done, retval=%u", retval);
	
	return retval;
}
//------------------------------------------------------------------------------


void runtime_launch_guest(void){

printf("\nlaunch: clearing VMCS...");	
asm(" vmclear guest_region			\n"
		" jbe	vt_vmfail				\n");
printf("Done.");		


memset( (void *)(u32)guest_region, 0, 0x1000);
memcpy( (void *)(u32)guest_region, msr0x480, 4);

printf("\nlaunch: loading VMPTR...");		
asm(" vmptrld guest_region			\n"
		" jbe	vt_vmfail				\n");
printf("Done.");

printf("\nlaunch: writing VMCS fields...");
asm("  xor	%%edx, %%edx			\n"
		"  mov	elements, %%ecx			\n"
		"nxwr:					\n"
		"  mov	machine+0(%%edx), %%eax		\n"
		"  mov	machine+4(%%edx), %%ebx		\n"
		"  vmwrite (%%ebx), %%eax			\n"
		"  jbe	vt_vmfail				\n"
		"  add	$8, %%edx			\n"
		"  loop	nxwr				\n" ::: "eax", "ebx", "ecx", "edx");
printf("Done.");		

printf("\nlaunch: VMLAUNCH...");

asm(" mov  guest_RAX, %eax			\n"
		" mov  guest_RBX, %ebx			\n"
		" mov  guest_RCX, %ecx			\n"
		" mov  guest_RDX, %edx			\n"
		" mov  guest_RBP, %ebp			\n"
		" mov  guest_RSI, %esi			\n"
		" mov  guest_RDI, %edi			\n"
		" vmlaunch				\n"
		" jmp  vt_vmfail				\n");

}


static const u32 vmx_msr_index[] = {
	MSR_EFER, MSR_K6_STAR
};

#define NUM_VMX_MSR (sizeof(vmx_msr_index)/sizeof(vmx_msr_index[0]))

struct msr_entry {
	u32 index;
	u32 reserved;
	u64 data;
};

extern u32 __msr_area_host[], __msr_area_guest[];
extern u32 __vmx_io_bitmap[];

//------------------------------------------------------------------------------
//isl_prepareVMCS
//prepareVMCS for guest execution
//inputs: currentstate = current state of guest, nextstate= desired state
//returns the new currentstate
u32 isl_prepareVMCS(u32 currentstate, u32 nextstate){
	
	if(currentstate == GSTATE_DEAD){
		ASSERT((nextstate == GSTATE_REALMODE));
		//setup VMCS
		{
			//setup host state
			asm(" mov %%cr0, %%eax \n mov %%eax, host_CR0 " ::: "ax" );	
			asm(" mov %%cr4, %%eax \n mov %%eax, host_CR4 " ::: "ax" );	
			asm(" mov %%cr3, %%eax \n mov %%eax, host_CR3 " ::: "ax" );	
			asm(" mov %es, host_ES_selector ");
			asm(" mov %cs, host_CS_selector ");
			asm(" mov %ss, host_SS_selector ");
			asm(" mov %ds, host_DS_selector ");
			asm(" mov %fs, host_FS_selector ");
			asm(" mov %gs, host_GS_selector ");
			asm(" str host_TR_selector ");
			host_GDTR_base = (u64)(u32)__runtimegdt_start;
			host_IDTR_base = (u64)(u32)__runtimeidt_start;
			host_TR_base = (u64)(u32)__runtimetss;
			host_RIP = (u64)(u32)__islayer_callback;
			host_RSP = (u64)(u32)runtime_stack + (u64)__RUNTIMESTACK_SIZE;
			asm(	" mov	$0x174, %%ecx			\n"\
						" rdmsr					\n"\
						" mov	%%eax, host_SYSENTER_CS		\n"\
						" inc	%%ecx				\n"\
						" rdmsr					\n"\
						" mov	%%eax, host_SYSENTER_ESP+0	\n"\
						" mov	%%edx, host_SYSENTER_ESP+4	\n"\
						" inc	%%ecx				\n"\
						" rdmsr					\n"\
						" mov	%%eax, host_SYSENTER_EIP+0	\n"\
						" mov	%%edx, host_SYSENTER_EIP+4	\n"\
						::: "ax", "cx", "dx" );
			asm(	" mov	$0xC0000100, %%ecx		\n"\
						" rdmsr					\n"\
						" mov	%%eax, host_FS_base+0		\n"\
						" mov	%%edx, host_FS_base+4		\n"\
						" inc	%%ecx				\n"\
						" rdmsr					\n"\
						" mov	%%eax, host_GS_base+0		\n"\
						" mov	%%edx, host_GS_base+4		\n"\
						::: "ax", "cx", "dx" );


			//setup guest state
				//setup paging structures 1:1 mapping, non-PAE
				{
					u32	*pgdir, *pgtbl;
					u32 i;
					
					pgdir = (u32 *)__runtime_v86_pagedir;
					for (i = 0; i < 1024; i++)
						pgdir[ i ] = ((u32)__runtime_v86_pagetables + (i*4096)) | 0x007;
			
					pgtbl = (u32 *)__runtime_v86_pagetables;
					for (i = 0; i < (1024*1024); i++){
						u32 page_address = (i << 12); 
						pgtbl[ i ] = page_address | 0x007;
					}
				}
	
				//setup IDT
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
							desc |= (__SELECTOR_CODE << 16);
							desc |= (0xEE00ULL << 32);	// DPL=3, 386-INTR-gate
							g_idt[ 13 ] = desc;		// General Protection Fault		
						}else{
							desc = (u64)(u32)fptr[i]; 	// offset for int stub
							desc &= 0x00000000FFFFFFFFULL;
							desc |= (desc << 32);
							desc &= 0xFFFF00000000FFFFULL; 
							desc |= (__SELECTOR_CODE << 16);
							desc |= (0xEE00ULL << 32);	// DPL=3, 386-INTR-gate
							g_idt[i] = desc;		// INT 		
						}
					}
				}

				//setup GDT
				{
					u64 *g_gdt;
					u64 desc;
					memset((void *)__runtime_v86_gdt, 0, 0x1000);
					g_gdt = (u64 *)(u32)__runtime_v86_gdt;
					desc = (u64)(u32)__runtime_v86_tss;
					desc = ((desc & 0xFF000000)<<32)|((desc & 0x00FFFFFF)<<16);
					desc |= ( 8328 ) | (0x008BULL << 40);
					g_gdt[ __SELECTOR_TASK >> 3 ] = desc;
			
					desc = (u64)(u32)__runtime_v86_ldt;
					desc = ((desc & 0xFF000000)<<32)|((desc & 0x00FFFFFF)<<16);
					desc |= ( 4 * 8 - 1) | (0x0082ULL << 40);
					g_gdt[ __SELECTOR_LDTR >> 3 ] = desc;
				}

				//setup LDT
				{
					u64 *g_ldt;
					u64 desc;
					memset((void *)__runtime_v86_ldt, 0, 0x1000);
					g_ldt = (u64 *)(u32)__runtime_v86_ldt;
					desc = 0x00CF9A000000FFFFLL;
					g_ldt[ __SELECTOR_CODE >> 3 ] = desc;
					desc = 0x00CF92000000FFFFLL;
					g_ldt[ __SELECTOR_DATA >> 3 ] = desc; 
					desc = 0x0000920B8000FFFFLL;
					g_ldt[ __SELECTOR_VRAM >> 3 ] = desc;
					desc = 0x00CF92000000FFFFLL;
					g_ldt[ __SELECTOR_FLAT >> 3 ] = desc;
				}	

				//setup TSS
				{
					u32 *g_tss;
					memset((void *)__runtime_v86_tss, 0, 0x4000);
					g_tss = (u32 *)__runtime_v86_tss;
					g_tss[0] = 0;			// back-link
					g_tss[1] = (u32)__runtime_v86_ring0stack + 0x4000; // ESP0
					g_tss[2] = __SELECTOR_FLAT;	           // SS0
					g_tss[25] = 0x00880000;		// IOBITMAP offset
					// number of bytes in TSS: 104 + 32 + 8192 = 8328
					g_tss[ 8328 >> 2 ] = 0xFF;	// end of IOBITMAP
				}
	
				//setup registers
				guest_ES_selector = 0x0000;

#if defined(__CONF_GUESTOS_LINUX__)
				guest_CS_selector = LINUX_BOOT_CS;
				guest_SS_selector = LINUX_BOOT_DS;
				guest_DS_selector = LINUX_BOOT_DS;
#else
				guest_CS_selector = 0x0000;
				guest_SS_selector = 0x6000;
				guest_DS_selector = 0x0000;
#endif
				guest_FS_selector = 0x0000;
				guest_GS_selector = 0x0000;
				guest_RAX = 0;
				guest_RBX = 0;
				guest_RCX = 0;
				guest_RDX = 0;
				guest_RBP = 0;
				guest_RSI = 0;
				guest_RDI = 0;
#if defined(__CONF_GUESTOS_LINUX__)
				guest_RSP = LINUX_BOOT_SP;
				guest_RIP = 0x0000;
#else
				guest_RSP = 0x4000;
				guest_RIP = 0x7c00;
#endif				
				guest_RFLAGS = 0; 
				guest_RFLAGS &= ~((1<<3)|(1<<5)|(1<<15));	// reserved 0-bits
				guest_RFLAGS |= (1<<1);				// reserved 1-bits
				guest_RFLAGS |= (1<<17);			// Virtual-8086 = enable
				guest_RFLAGS |= (3<<12);			// IO-privilege-level = 3 

#if !defined(__CONF_GUESTOS_LINUX__)
				guest_RFLAGS |= (1<<9);				// IF = enable 
#endif

				guest_RFLAGS &= ~(1<<14);			// Nested Task = disable
				
				guest_ES_base = (guest_ES_selector << 4);
				guest_CS_base = (guest_CS_selector << 4);
				guest_SS_base = (guest_SS_selector << 4);
				guest_DS_base = (guest_DS_selector << 4);
				guest_FS_base = (guest_FS_selector << 4);
				guest_GS_base = (guest_GS_selector << 4);
				guest_ES_limit = 0xFFFF;
				guest_CS_limit = 0xFFFF;
				guest_SS_limit = 0xFFFF;
				guest_DS_limit = 0xFFFF;
				guest_FS_limit = 0xFFFF;
				guest_GS_limit = 0xFFFF;
				guest_ES_access_rights = 0xF3;
				guest_CS_access_rights = 0xF3;
				guest_SS_access_rights = 0xF3;
				guest_DS_access_rights = 0xF3;
				guest_FS_access_rights = 0xF3;
				guest_GS_access_rights = 0xF3;
				
				guest_CR0 = msr0x480[6];
				guest_CR4 = msr0x480[8];
				
				guest_CR3 = (u32)__runtime_v86_pagedir;
				guest_VMCS_link_pointer_full = ~0L;
				guest_VMCS_link_pointer_high = ~0L;
				guest_IDTR_base = (u32)__runtime_v86_idt;
				guest_GDTR_base = (u32)__runtime_v86_gdt;
				guest_LDTR_base = (u32)__runtime_v86_ldt;
				guest_TR_base   = (u32)__runtime_v86_tss;
				guest_IDTR_limit = (256 * 8) - 1;	// 256 descriptors
				guest_GDTR_limit = (3 * 8) - 1;		// 3 descriptors
				guest_LDTR_limit = (4 * 8) - 1;		// 4 descriptors
				guest_TR_limit   = (26 * 4) + 0x20 + 0x2000;
				guest_LDTR_access_rights = 0x82;
				guest_TR_access_rights   = 0x8B;
				guest_LDTR_selector = __SELECTOR_LDTR;
				guest_TR_selector   = __SELECTOR_TASK;

				//setup VMX controls
				control_VMX_pin_based = msr0x480[ 1 ];
				control_VMX_cpu_based = msr0x480[ 2 ];
				control_VM_exit_controls = msr0x480[ 3 ];
				control_VM_entry_controls = msr0x480[ 4 ];
				control_VMX_cpu_based |= (1<<7);	// HLT-exiting
				//control_CR0_mask   = 0x80000021;
				control_CR0_mask = msr0x480[6];
	 			control_CR0_shadow = __V86M_CR0_INITVAL; //real-mode, no-paging
				
				//MSR load/store
				{
					u32 i, msr;
					u32 msrentry_host_paddr, msrentry_guest_paddr;
					struct msr_entry *hmsr, *gmsr;
					msrentry_host_paddr = (u32)__msr_area_host;
					msrentry_guest_paddr = (u32)__msr_area_guest;
					
					
					printf("\nMSR load/store populate:");
					//store initial values of the MSRs
					for(i=0; i < NUM_VMX_MSR; i++){
						u32 eax, edx;
						hmsr = (struct msr_entry *)msrentry_host_paddr;
						gmsr = (struct msr_entry *)msrentry_guest_paddr;
						msr = vmx_msr_index[i];						
						rdmsr(msr, &eax, &edx);
						hmsr->index = gmsr->index = msr;
						hmsr->data = gmsr->data = ((u64)edx << 32) | (u64)eax;
						
						printf("\nMSR host_index=0x%08x, host_data=0x%016llx", hmsr->index, hmsr->data);
						printf("\nMSR guest_index=0x%08x, guest_data=0x%016llx", gmsr->index, gmsr->data);
						
						msrentry_host_paddr += sizeof(struct msr_entry);
						msrentry_guest_paddr += sizeof(struct msr_entry);
					}
					
					
					//host MSR load on exit, we store it ourselves before entry
					control_VM_exit_MSR_load_address_full=(u32)__msr_area_host;
					control_VM_exit_MSR_load_address_high=0;
					control_VM_exit_MSR_load_count=NUM_VMX_MSR;
					
					//guest MSR load on entry, store on exit
					control_VM_entry_MSR_load_address_full=(u32)__msr_area_guest;
					control_VM_entry_MSR_load_address_high=0;
					control_VM_entry_MSR_load_count=NUM_VMX_MSR;
				  control_VM_exit_MSR_store_address_full=(u32)__msr_area_guest;
					control_VM_exit_MSR_store_address_high=0;
					control_VM_exit_MSR_store_count=NUM_VMX_MSR;
					
				
				}
				
				//IO bitmap support
				memset( (void *)__vmx_io_bitmap, 0, (PAGE_SIZE_4K * 2));
				control_IO_BitmapA_address_full = (u32)__vmx_io_bitmap;
				control_IO_BitmapA_address_high = 0;
				control_IO_BitmapB_address_full = (u32)__vmx_io_bitmap + PAGE_SIZE_4K;
				control_IO_BitmapB_address_high = 0;
				control_VMX_cpu_based |= (1 << 25); //enable use IO Bitmaps
				
				
				
				
				//setup IO intercepts
				islayer_set_ioport_intercept(ACPI_CONTROLREG_PORT);
				//islayer_set_ioport_intercept(ACPI_STATUSREG_PORT);

				
					control_pagefault_errorcode_mask  = 0x00000000;	//dont be concerned with 
					control_pagefault_errorcode_match = 0x00000000; //guest page-faults
					control_exception_bitmap = 0;
					control_CR3_target_count = 0;

					control_CR4_mask   = msr0x480[8] | CR4_PAE; //we want to intercept access to these bits 
	 				control_CR4_shadow = CR4_VMXE; //let guest know we have VMX enabled
				
					//control_VMX_cpu_based &= ~(1 << 15); //disable CR3 load exiting
					//control_VMX_cpu_based &= ~(1 << 16); //disable CR3 store exiting
 
					control_VMX_cpu_based |= (1 << 15); //enable CR3 load exiting
					control_VMX_cpu_based |= (1 << 16); //enable CR3 store exiting


		} //setup VMCS		
	
	
		//debug
		printf("\nDEAD --> REAL (CS:IP=0x%04x:0x%04x, SS:SP=0x%04x:0x%04x)",
						(u16)guest_CS_selector, (u16)guest_RIP, (u16)guest_SS_selector, (u16)guest_RSP );

	
		return(nextstate);
		// END if(currentstate == GSTATE_DEAD)
	}else if(currentstate == GSTATE_REALMODE){
		ASSERT( (nextstate == GSTATE_PROTECTEDMODE) ||
			(nextstate == (GSTATE_PROTECTEDMODE | GSTATE_PROTECTEDMODE_PG) )
			);
	
		//guest has loaded a GDT, might have loaded IDT and set PG, but before
		//the GDT can take effect, the guest usually performs a long jump or
		//a retf. So, we have to plug in temporary CS and SS selectors
		//defined with 64K limit until the long jump or retf is performed. 
		//We set our CS and SS selectors above the limit already loaded by
		//the guest. This way we can be sure that our selector values do not
		//collide with guest selector values and we will always get a general
		//protection fault (#GP, 0x0D) when the guest tries to do a 
		//far jump or retf
		
		//setup VMCS controls
		control_VMX_cpu_based &= ~(1<<7);	// clear HLT-exiting
		control_exception_bitmap |= (1UL << 13); //set INT 13 (#GP fault)
		
		//setup guest portion
		{
			//setup GDT
			{
					u64 *gdt;
					u64 desc;
					memset((void *)__limbo_gdt, __LIMBO_GDT_SIZE, 0);
					gdt = (u64 *)(u32)__limbo_gdt;
					ASSERT( (v86monitor_guest_gdt_base != 0) && 
									(v86monitor_guest_gdt_limit != 0) );
					guest_CS_selector = (v86monitor_guest_gdt_limit + 1) + 0x08;								
					guest_SS_selector = (v86monitor_guest_gdt_limit + 1) + 0x10;
					guest_TR_selector = (v86monitor_guest_gdt_limit + 1) + 0x18;
					//printf("\nguest gdt: base=0x%08lx, size=0x%04x",
					//	(unsigned long)v86monitor_guest_gdt_base, 
					//	(unsigned short)v86monitor_guest_gdt_limit);
					//printf("\nlimbo selectors: CS=0x%04x, SS=0x%04x, TR=0x%04x",
					//	(unsigned short)guest_CS_selector, 
					//	(unsigned short)guest_SS_selector,
					//	(unsigned short)guest_TR_selector);

					//printf("\nguest segment registers: CS=0x%04x, SS=0x%04x",
					//	(unsigned short)v86monitor_guest_reg_cs, 
					//	(unsigned short)v86monitor_guest_reg_ss);

					desc = (u64)(u32)(v86monitor_guest_reg_cs * 16);
					desc = ((desc & 0xFF000000)<<32)|((desc & 0x00FFFFFF)<<16);
					desc |= 0xFFFF | ( 0x009BULL << 40);
					gdt[guest_CS_selector >> 3] = desc;

					desc = (u64)(u32)(v86monitor_guest_reg_ss * 16);
					desc = ((desc & 0xFF000000)<<32)|((desc & 0x00FFFFFF)<<16);
					desc |= 0xFFFF | ( 0x0093ULL << 40);
					gdt[guest_SS_selector >> 3] = desc;
			
					guest_GDTR_base = (u32)__limbo_gdt;
					guest_GDTR_limit = __LIMBO_GDT_SIZE - 1;
			}
			
			if(isl_guesthastr == 1){
				guest_TR_selector=isl_guest_TR_selector;
				guest_TR_base = isl_guest_TR_base;
				guest_TR_limit = isl_guest_TR_limit;
				guest_TR_access_rights = isl_guest_TR_access_rights;
				guest_LDTR_selector=isl_guest_LDTR_selector;
				guest_LDTR_base = isl_guest_LDTR_base;
				guest_LDTR_limit = isl_guest_LDTR_limit;
				guest_LDTR_access_rights = isl_guest_LDTR_access_rights;
			}else{
				//zero out LDTR 
				guest_LDTR_selector=0;
				guest_LDTR_base = 0;
				guest_LDTR_limit = 0;
				guest_LDTR_access_rights = 0x10000;
			
			}
			
			//always use limbo pages until we get to proper protected mode
			//printf("\nUsing limbo pages until we get to proper PMODE...");
			guest_CR3 = (u32)__runtime_v86_pagedir;
				
			//always make sure we have no IDT, we will load IDT when the
			//guest enters into proper protected-mode from limbo
			guest_IDTR_base = 0;
			guest_IDTR_limit = 0;
				
				
			//load guest CR0 and CR4, the v86 monitor has these values
			//stored when it performed a world switch
			guest_CR4 = v86monitor_guest_reg_cr4;
			guest_CR0 = v86monitor_guest_reg_cr0;
			//sanitize CR0 and CR4 values for VMX compatibility
			guest_CR4 |= msr0x480[8];
			guest_CR0 |= msr0x480[6];
				
			//set CR0.WP
			//guest_CR0 |= CR0_WP;
			

			//printf("\nCR0=0x%08lx, CR3=0x%08lx, CR4=0x%08lx",
			//	(unsigned long)guest_CR0, (unsigned long)guest_CR3, 
			//	(unsigned long)guest_CR4);
			
				guest_ES_selector = 0;
				guest_DS_selector = 0;
				guest_FS_selector = 0;
				guest_GS_selector = 0;
				guest_RAX = v86monitor_guest_reg_eax;
				guest_RBX = v86monitor_guest_reg_ebx;
				guest_RCX = v86monitor_guest_reg_ecx;
				guest_RDX = v86monitor_guest_reg_edx;
				guest_RBP = v86monitor_guest_reg_ebp;
				guest_RSI = v86monitor_guest_reg_esi;
				guest_RDI = v86monitor_guest_reg_edi;
				guest_RSP = v86monitor_guest_reg_esp;
				guest_RIP = v86monitor_guest_reg_eip;
				
				guest_RFLAGS = v86monitor_guest_reg_eflags; 
				guest_RFLAGS &= ~((1<<3)|(1<<5)|(1<<15));	// reserved 0-bits
				guest_RFLAGS |= (1<<1);				// reserved 1-bits
				guest_RFLAGS &= ~(1<<17);	// Virtual-8086 mode = disable
				guest_RFLAGS &= ~(3<<12);	// IOPL=0 
				//guest_RFLAGS &= ~(1<<9);	// IF disable 
				//guest_RFLAGS &= ~(1<<14);	// NT (Nested Task) disable
				
				guest_ES_base = 0;
				guest_CS_base = (u32)(v86monitor_guest_reg_cs * 16);
				guest_SS_base = (u32)(v86monitor_guest_reg_ss * 16);
				guest_DS_base = 0;
				guest_FS_base = 0;
				guest_GS_base = 0;
				guest_ES_limit = 0;
				guest_CS_limit = 0xFFFF;
				guest_SS_limit = 0xFFFF;
				guest_DS_limit = 0;
				guest_FS_limit = 0;
				guest_GS_limit = 0;
				guest_ES_access_rights = 0x10000;
				guest_CS_access_rights = 0x9B;
				guest_SS_access_rights = 0x93;
				guest_DS_access_rights = 0x10000;
				guest_FS_access_rights = 0x10000;
				guest_GS_access_rights = 0x10000;
				guest_VMCS_link_pointer_full = ~0L;
				guest_VMCS_link_pointer_high = ~0L;

		control_VMX_cpu_based |= (1 << 15); //enable CR3 load exiting
		control_VMX_cpu_based |= (1 << 16); //enable CR3 store exiting


		//debug
		//printf("\nREAL --> PROTECTED_LIMBO (CS:IP=0x%04x:0x%04x, SS:SP=0x%04x:0x%04x)",
		//				(u16)guest_CS_selector, (u16)guest_RIP, (u16)guest_SS_selector, (u16)guest_RSP );


			return(nextstate);
		}	
	// END if(currentstate == GSTATE_REALMODE)
	}else if(currentstate & GSTATE_PROTECTEDMODE){
		//see if we have no GDTR, if so this is a limbo to proper
		//stage, so we just load the GDTR and an optional IDTR if present
		//and setup paging
		if( !(currentstate & GSTATE_PROTECTEDMODE_GDTR) ){
			u64 *gdt;
			u64 desc;
			u32 gran;
			ASSERT(nextstate & GSTATE_PROTECTEDMODE_GDTR);
			
			//debug
			printf("\nPROTECTED_LIMBO --> PROTECTED");
			//printf("\n	SS:ESP before=0x%04x:0x%08x", guest_SS_selector, (u32)guest_RSP);
			//printf("\n	CS:EIP before=0x%04x:0x%08x", guest_CS_selector, (u32)guest_RIP);

			//printf("\nEntering proper protected mode from limbo");
			//printf("\n	Target CS:EIP=0x%04x:0x%08x",
			//	guest_limbo_cs, guest_limbo_eip);
			printf("\n	GUEST GDT load (base=0x%08x, limit=0x%04x)",
					v86monitor_guest_gdt_base, v86monitor_guest_gdt_limit);
			guest_GDTR_base = v86monitor_guest_gdt_base;
			guest_GDTR_limit = v86monitor_guest_gdt_limit;
			if(nextstate & GSTATE_PROTECTEDMODE_IDTR){
				printf("\n	GUEST IDT load (base=0x%08x, limit=0x%04x)",
					v86monitor_guest_idt_base, v86monitor_guest_idt_limit);
				guest_IDTR_base = v86monitor_guest_idt_base;
				guest_IDTR_limit = v86monitor_guest_idt_limit;
			}else{
				ASSERT( !(guest_RFLAGS & EFLAGS_IF) );
				//printf("\n 	NO IDT currently, but interrupts disabled, so no issues");
			}

			guest_SS_base =0;
			guest_SS_limit =0;
			guest_SS_access_rights=0x10000;
			guest_SS_selector = 0;
			guest_CS_selector = guest_limbo_cs;
			gdt = (u64 *)(u32)guest_GDTR_base;
			desc = gdt[guest_CS_selector >> 3];

			guest_CS_base = (u32) ( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
			guest_CS_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
			gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
			
			//gran = 1 ? (gran == 0) : 4096;
			//guest_CS_limit = (guest_CS_limit * gran);
			//if(gran == 4096)
			//	guest_CS_limit += 0xFFF;
			//printf("\n	guest_CS_limit=0x%08x, gran=%u", guest_CS_limit, gran);
			if( (gran==1) && (guest_CS_limit == 0x000FFFFFUL) )
				guest_CS_limit = 0xFFFFFFFFUL;
			
			guest_CS_access_rights = 
				(u32) (((u64)desc & (u64)0x00F0FF0000000000ULL) >> (u64)40);							
			
			
			//printf("\n	Guest CS base=0x%08x", guest_CS_base);
			//printf("\n	Guest CS limit=0x%08x", guest_CS_limit);
			//printf("\n	Guest CS access_rights=0x%08x", guest_CS_access_rights);
			
			
			guest_RIP = guest_limbo_eip;
			
			
			guest_ES_selector = 0;
				guest_DS_selector = 0;
				guest_FS_selector = 0;
				guest_GS_selector = 0;
				guest_RFLAGS &= ~((1<<3)|(1<<5)|(1<<15));	// reserved 0-bits
				guest_RFLAGS |= (1<<1);				// reserved 1-bits
				guest_ES_base = 0;
				guest_DS_base = 0;
				guest_FS_base = 0;
				guest_GS_base = 0;
				guest_ES_limit = 0;
				guest_DS_limit = 0;
				guest_FS_limit = 0;
				guest_GS_limit = 0;
				guest_ES_access_rights = 0x10000;
				
				//adjust CS access rights
				guest_CS_access_rights |= 0x0B;
				
				
				guest_SS_access_rights = 0x10000;
				guest_DS_access_rights = 0x10000;
				guest_FS_access_rights = 0x10000;
				guest_GS_access_rights = 0x10000;
				guest_VMCS_link_pointer_full = ~0L;
				guest_VMCS_link_pointer_high = ~0L;
			
			//printf("\nCS base=0x%08lx, limit=0x%08lx, gran=0x%08lx, acc=0x%08lx", (unsigned long)guest_CS_base,
			//	 	(unsigned long)guest_CS_limit,
			//		 (unsigned long)gran,
			//		 (unsigned long)guest_CS_access_rights);
		
			control_exception_bitmap &= ~(1UL << 13); //disable INT 13 (#GP fault)
			
			if(nextstate & GSTATE_PROTECTEDMODE_PG){
					//printf("\nGuest has pagetables, using CR3=0x%08lx",
					//	(unsigned long)v86monitor_guest_reg_cr3);
					
					guest_CR3  = v86monitor_guest_reg_cr3;
			}else{
				//guest must be enabling paging by setting CR0.PG later
				guestcr3val_when_cr0_pg_off = v86monitor_guest_reg_cr3;
			}
			
			//setup guest RSP
			guest_RSP |= limbo_rsp;

			//debug
			//printf("\n	SS:ESP after=0x%04x:0x%08x", guest_SS_selector, (u32)guest_RSP);
			//printf("\n	CS:EIP after=0x%04x:0x%08x", guest_CS_selector, (u32)guest_RIP);



			return (nextstate);
		}else if(nextstate == GSTATE_REALMODE){
			//debug
			printf("\nPROTECTED --> REAL");
			//printf("\n	SS:ESP before=0x%04x:0x%08x", guest_SS_selector, (u32)guest_RSP);
			//printf("\n	CS:EIP before=0x%04x:0x%08x", guest_CS_selector, (u32)guest_RIP);

			
			//prepare to lock in V86 monitor, all state is already initialized,
			//all we need to do is to initialize the registers
			//load all the segment register base, limits and access rights from 
			//the current selector values

			//loading the v86 monitor destroys LDTR and TR which can be
			//persistent across prot-real-prot if unchanged, so we need to
			//save them here
			isl_guest_TR_selector=guest_TR_selector;
			isl_guest_TR_base = guest_TR_base;
			isl_guest_TR_limit = guest_TR_limit;
			isl_guest_TR_access_rights = guest_TR_access_rights;
			isl_guest_LDTR_selector=guest_LDTR_selector;
			isl_guest_LDTR_base = guest_LDTR_base;
			isl_guest_LDTR_limit = guest_LDTR_limit;
			isl_guest_LDTR_access_rights = guest_LDTR_access_rights;
			isl_guesthastr=1;
					
							
			//save current CR3 value
			v86monitor_guest_reg_cr3 = guest_CR3;
			
			//setup segment registers			
			{
				u64 *gdt;
				u64 desc;
				u32 gran;
				gdt = (u64 *)(u32)guest_GDTR_base;
			
				//CS	
				desc = gdt[guest_CS_selector >> 3];
				guest_CS_base = (u32) 
								( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
				guest_CS_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
				gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
				gran = 1 ? (gran == 0) : 4096;
				guest_CS_limit = (guest_CS_limit * gran);
				if(gran == 4096)
					guest_CS_limit += 0xFFF;
				guest_CS_access_rights = 
					(u32) (((u64)desc & 0x00FFFF0000000000ULL) >> (u64)40);							

				//DS	
				desc = gdt[guest_DS_selector >> 3];
				guest_DS_base = (u32) 
								( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
				guest_DS_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
				gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
				gran = 1 ? (gran == 0) : 4096;
				guest_DS_limit = (guest_DS_limit * gran);
				if(gran == 4096)
					guest_DS_limit += 0xFFF;
				guest_DS_access_rights = 
					(u32) (((u64)desc & 0x00FFFF0000000000ULL) >> (u64)40);							

				//ES	
				desc = gdt[guest_ES_selector >> 3];
				guest_ES_base = (u32) 
								( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
				guest_ES_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
				gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
				gran = 1 ? (gran == 0) : 4096;
				guest_ES_limit = (guest_ES_limit * gran);
				if(gran == 4096)
					guest_ES_limit += 0xFFF;
				guest_ES_access_rights = 
					(u32) (((u64)desc & 0x00FFFF0000000000ULL) >> (u64)40);							
			
				//FS	
				desc = gdt[guest_FS_selector >> 3];
				guest_FS_base = (u32) 
								( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
				guest_FS_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
				gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
				gran = 1 ? (gran == 0) : 4096;
				guest_FS_limit = (guest_FS_limit * gran);
				if(gran == 4096)
					guest_FS_limit += 0xFFF;
				guest_FS_access_rights = 
					(u32) (((u64)desc & 0x00FFFF0000000000ULL) >> (u64)40);							

				//GS	
				desc = gdt[guest_GS_selector >> 3];
				guest_GS_base = (u32) 
								( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
				guest_GS_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
				gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
				gran = 1 ? (gran == 0) : 4096;
				guest_GS_limit = (guest_GS_limit * gran);
				if(gran == 4096)
					guest_GS_limit += 0xFFF;
				guest_GS_access_rights = 
					(u32) (((u64)desc & 0x00FFFF0000000000ULL) >> (u64)40);							

				//SS	
				desc = gdt[guest_SS_selector >> 3];
				guest_SS_base = (u32) 
								( (((u64)desc & 0x000000FFFFFF0000ULL) >> (u64)16) |
									(((u64)desc & 0xFF00000000000000ULL) >> (u64)32) );
				guest_SS_limit = (u32) ( ((u64)desc & 0x000000000000FFFFULL) | 
						         (((u64)desc & 0x000F000000000000ULL) >> (u64)32) );
				gran = (u32) (((u64)desc & 0x00F0000000000000ULL) >> (u64)55);
				gran = 1 ? (gran == 0) : 4096;
				guest_SS_limit = (guest_SS_limit * gran);
				if(gran == 4096)
					guest_SS_limit += 0xFFF;
				guest_SS_access_rights = 
					(u32) (((u64)desc & 0x00FFFF0000000000ULL) >> (u64)40);							
			
			}


			if(guest_RFLAGS & (1 << 14)){
				printf("\nGuest has NT bit set, hmm gotta handle this!");
				HALT();
			}

			if(guest_RFLAGS & (3 << 12)){
				printf("\nGuest has IOPL 3, hmm gotta handle this!");
				HALT();
			}

			guest_RFLAGS &= ~((1<<3)|(1<<5)|(1<<15));	// reserved 0-bits
			guest_RFLAGS |= (1<<1);				// reserved 1-bits
			guest_RFLAGS |= (1<<17);	// for Virtual-8086 mode
			guest_RFLAGS |= (3<<12);	// for IO-privilege-level 
			
			


			guest_RFLAGS &= ~(1<<14);	// for NT (Nested Task)
			
			//sanitize guest CR0 for VMX compatibility
			guest_CR0 |= msr0x480[6];
			//guest_CR0 |= CR0_WP;
			
			guest_CR3 = (u32)__runtime_v86_pagedir;
			guest_VMCS_link_pointer_full = ~0L;
			guest_VMCS_link_pointer_high = ~0L;
			guest_IDTR_base = (u32)__runtime_v86_idt;
			guest_GDTR_base = (u32)__runtime_v86_gdt;
			guest_LDTR_base = (u32)__runtime_v86_ldt;
			guest_TR_base   = (u32)__runtime_v86_tss;
			guest_IDTR_limit = (256 * 8) - 1;	// 256 descriptors
			guest_GDTR_limit = (3 * 8) - 1;		// 3 descriptors
			guest_LDTR_limit = (4 * 8) - 1;		// 4 descriptors
			guest_TR_limit   = (26 * 4) + 0x20 + 0x2000;
			guest_LDTR_access_rights = 0x82;
			guest_TR_access_rights   = 0x8B;
			guest_LDTR_selector = __SELECTOR_LDTR;
			guest_TR_selector   = __SELECTOR_TASK;
			guest_ES_access_rights = 0xF3;
			guest_CS_access_rights = 0xF3;
			guest_SS_access_rights = 0xF3;
			guest_DS_access_rights = 0xF3;
			guest_FS_access_rights = 0xF3;
			guest_GS_access_rights = 0xF3;
			guest_CS_selector=guest_CS_base >> 4;
			guest_DS_selector=guest_DS_base >> 4;
			guest_ES_selector=guest_ES_base >> 4;
			guest_FS_selector=guest_FS_base >> 4;
			guest_GS_selector=guest_GS_base >> 4;
			guest_SS_selector=guest_SS_base >> 4;
			
			limbo_rsp = guest_RSP;
			limbo_rsp &= 0xFFFF0000; //clear low 16-bits
			guest_RSP &= 0x0000FFFF; //clear high 16 bits for guest

			control_VMX_cpu_based |= (1<<7);	// HLT-exiting

			//printf("\n	SS:SP after=0x%04x:0x%08x", (u16)guest_SS_selector, (u16)guest_RSP);
			//printf("\n	CS:IP after=0x%04x:0x%04x",	(u16)guest_CS_selector, (u16)guest_RIP);
			

			return(nextstate);
		}

	}

	printf("\nisl_prepareVMCS: invalid combination: 0x%08lx->0x%08lx",
		(unsigned long)currentstate, (unsigned long)nextstate);
	HALT();
	return(GSTATE_DEAD);
}



//guest state variables
u32 guest_currentstate = GSTATE_DEAD;			//current operating mode of guest
u32 guest_nextstate = GSTATE_REALMODE;		//next operating mode of guest

//------------------------------------------------------------------------------
// guest VMCS fields
// Natural 32-bit Control fields

unsigned int  control_VMX_pin_based;
unsigned int  control_VMX_cpu_based;
unsigned int  control_exception_bitmap;
unsigned int  control_pagefault_errorcode_mask; 
unsigned int  control_pagefault_errorcode_match; 
unsigned int  control_CR3_target_count;
unsigned int  control_VM_exit_controls;
unsigned int  control_VM_exit_MSR_store_count;
unsigned int  control_VM_exit_MSR_load_count;
unsigned int  control_VM_entry_controls;
unsigned int  control_VM_entry_MSR_load_count;
unsigned int  control_VM_entry_interruption_information;
unsigned int  control_VM_entry_exception_errorcode;
unsigned int  control_VM_entry_instruction_length;
unsigned int  control_Task_PRivilege_Threshold;
// Natural 64-bit Control fields
unsigned long long  control_CR0_mask;
unsigned long long  control_CR4_mask;
unsigned long long  control_CR0_shadow;
unsigned long long  control_CR4_shadow;
unsigned long long  control_CR3_target0;
unsigned long long  control_CR3_target1;
unsigned long long  control_CR3_target2;
unsigned long long  control_CR3_target3;
// Full 64-bit Control fields
unsigned int  control_IO_BitmapA_address_full;
unsigned int  control_IO_BitmapA_address_high;
unsigned int  control_IO_BitmapB_address_full;
unsigned int  control_IO_BitmapB_address_high;
unsigned int  control_MSR_Bitmaps_address_full;
unsigned int  control_MSR_Bitmaps_address_high;
unsigned int  control_VM_exit_MSR_store_address_full;
unsigned int  control_VM_exit_MSR_store_address_high;
unsigned int  control_VM_exit_MSR_load_address_full;
unsigned int  control_VM_exit_MSR_load_address_high;
unsigned int  control_VM_entry_MSR_load_address_full;
unsigned int  control_VM_entry_MSR_load_address_high;
unsigned int  control_Executive_VMCS_pointer_full;
unsigned int  control_Executive_VMCS_pointer_high;
unsigned int  control_TSC_offset_full;
unsigned int  control_TSC_offset_high;
unsigned int  control_virtual_APIC_page_address_full;
unsigned int  control_virtual_APIC_page_address_high;

// Natural 64-bit Host-State fields
unsigned long long  host_CR0;
unsigned long long  host_CR3;
unsigned long long  host_CR4;
unsigned long long  host_FS_base;
unsigned long long  host_GS_base;
unsigned long long  host_TR_base;
unsigned long long  host_GDTR_base;
unsigned long long  host_IDTR_base;
unsigned long long  host_SYSENTER_ESP;
unsigned long long  host_SYSENTER_EIP;
unsigned long long  host_RSP;
unsigned long long  host_RIP;
// Natural 32-bit Host-State fields
unsigned int  host_SYSENTER_CS;
// Natural 16-bit Host-State fields
unsigned short  host_ES_selector;
unsigned short  host_CS_selector;
unsigned short  host_SS_selector;
unsigned short  host_DS_selector;
unsigned short  host_FS_selector;
unsigned short  host_GS_selector;
unsigned short  host_TR_selector;

// Natural 64-bit Guest-State fields
unsigned long long  guest_CR0;
unsigned long long  guest_CR3;
unsigned long long  guest_CR4;
unsigned long long  guest_ES_base;
unsigned long long  guest_CS_base; 
unsigned long long  guest_SS_base;
unsigned long long  guest_DS_base;
unsigned long long  guest_FS_base;
unsigned long long  guest_GS_base;
unsigned long long  guest_LDTR_base;
unsigned long long  guest_TR_base;
unsigned long long  guest_GDTR_base;
unsigned long long  guest_IDTR_base;
unsigned long long  guest_DR7;
unsigned long long  guest_RSP; 
unsigned long long  guest_RIP; 
unsigned long long  guest_RFLAGS; 
unsigned long long  guest_pending_debug_x;
unsigned long long  guest_SYSENTER_ESP;
unsigned long long  guest_SYSENTER_EIP;




// Natural 32-bit Guest-State fields
unsigned int  guest_ES_limit;
unsigned int  guest_CS_limit;
unsigned int  guest_SS_limit;
unsigned int  guest_DS_limit;
unsigned int  guest_FS_limit;
unsigned int  guest_GS_limit;
unsigned int  guest_LDTR_limit; 
unsigned int  guest_TR_limit;
unsigned int  guest_GDTR_limit;
unsigned int  guest_IDTR_limit;
unsigned int  guest_ES_access_rights; 
unsigned int  guest_CS_access_rights;
unsigned int  guest_SS_access_rights;
unsigned int  guest_DS_access_rights;
unsigned int  guest_FS_access_rights;
unsigned int  guest_GS_access_rights;
unsigned int  guest_LDTR_access_rights;
unsigned int  guest_TR_access_rights;
unsigned int  guest_interruptibility; 
unsigned int  guest_activity_state; 
unsigned int  guest_SMBASE;	// <-- Added 23 December 2006
unsigned int  guest_SYSENTER_CS; 
// Natural 16-bit Guest-State fields
unsigned short  guest_ES_selector;
unsigned short  guest_CS_selector;
unsigned short  guest_SS_selector;
unsigned short  guest_DS_selector;
unsigned short  guest_FS_selector;
unsigned short  guest_GS_selector;
unsigned short  guest_LDTR_selector;
unsigned short  guest_TR_selector;
// Full 64-bit Guest-State fields
unsigned int  guest_VMCS_link_pointer_full;
unsigned int  guest_VMCS_link_pointer_high;
unsigned int  guest_IA32_DEBUGCTL_full;
unsigned int  guest_IA32_DEBUGCTL_high;

//------------------
// Read-Only Fields
//------------------
unsigned int  info_vminstr_error;
unsigned int  info_vmexit_reason;
unsigned int  info_vmexit_interrupt_information;
unsigned int  info_vmexit_interrupt_error_code;
unsigned int  info_IDT_vectoring_information;
unsigned int  info_IDT_vectoring_error_code;
unsigned int  info_vmexit_instruction_length;
unsigned int  info_vmx_instruction_information;
unsigned long long  info_exit_qualification;
unsigned long long  info_IO_RCX;
unsigned long long  info_IO_RSI;
unsigned long long  info_IO_RDI;
unsigned long long  info_IO_RIP;
unsigned long long  info_guest_linear_address;


VMCS_DEF  machine[] =	{
	//----------------
	// Control fields
	//----------------

	// Natural 32-bit Control fields
	{ 0x4000, &control_VMX_pin_based },
	{ 0x4002, &control_VMX_cpu_based },

	{ 0x4004, &control_exception_bitmap },
	{ 0x4006, &control_pagefault_errorcode_mask },
	{ 0x4008, &control_pagefault_errorcode_match },
	{ 0x400A, &control_CR3_target_count },
	{ 0x400C, &control_VM_exit_controls },
	{ 0x400E, &control_VM_exit_MSR_store_count },
	{ 0x4010, &control_VM_exit_MSR_load_count },
	{ 0x4012, &control_VM_entry_controls },
	{ 0x4014, &control_VM_entry_MSR_load_count },
	{ 0x4016, &control_VM_entry_interruption_information },
	{ 0x4018, &control_VM_entry_exception_errorcode },
	{ 0x401A, &control_VM_entry_instruction_length },
	{ 0x401C, &control_Task_PRivilege_Threshold },
	// Natural 64-bit Control fields
	{ 0x6000, &control_CR0_mask },
	{ 0x6002, &control_CR4_mask }, 
	{ 0x6004, &control_CR0_shadow },
	{ 0x6006, &control_CR4_shadow },
	{ 0x6008, &control_CR3_target0 },
	{ 0x600A, &control_CR3_target1 },
	{ 0x600C, &control_CR3_target2 },
	{ 0x600E, &control_CR3_target3 },
	// Full 64-bit Control fields
	{ 0x2000, &control_IO_BitmapA_address_full },
	{ 0x2001, &control_IO_BitmapA_address_high },
	{ 0x2002, &control_IO_BitmapB_address_full },
	{ 0x2003, &control_IO_BitmapB_address_high },
////	{ 0x2004, &control_MSR_Bitmaps_address_full },
////	{ 0x2005, &control_MSR_Bitmaps_address_high }, 
	{ 0x2006, &control_VM_exit_MSR_store_address_full },
	{ 0x2007, &control_VM_exit_MSR_store_address_high },
	{ 0x2008, &control_VM_exit_MSR_load_address_full },
	{ 0x2009, &control_VM_exit_MSR_load_address_high },
	{ 0x200A, &control_VM_entry_MSR_load_address_full },
	{ 0x200B, &control_VM_entry_MSR_load_address_high },
	{ 0x200C, &control_Executive_VMCS_pointer_full },
	{ 0x200D, &control_Executive_VMCS_pointer_high },
	{ 0x2010, &control_TSC_offset_full },
	{ 0x2011, &control_TSC_offset_high },
////	{ 0x2012, &control_virtual_APIC_page_address_full }, 
////	{ 0x2013, &control_virtual_APIC_page_address_high },

	//-------------------
	// Host-State fields
	//-------------------
	// Natural 64-bit Host-State fields
	{ 0x6C00, &host_CR0 },
	{ 0x6C02, &host_CR3 },
	{ 0x6C04, &host_CR4 },
	{ 0x6C06, &host_FS_base },
	{ 0x6C08, &host_GS_base },
	{ 0x6C0A, &host_TR_base },
	{ 0x6C0C, &host_GDTR_base },
	{ 0x6C0E, &host_IDTR_base },
	{ 0x6C10, &host_SYSENTER_ESP },
	{ 0x6C12, &host_SYSENTER_EIP },
	{ 0x6C14, &host_RSP },
	{ 0x6C16, &host_RIP },
	// Natural 32-bit Host-State fields
	{ 0x4C00, &host_SYSENTER_CS },
	// Natural 16-bit Host-State fields
	{ 0x0C00, &host_ES_selector },
	{ 0x0C02, &host_CS_selector },
	{ 0x0C04, &host_SS_selector },
	{ 0x0C06, &host_DS_selector },
	{ 0x0C08, &host_FS_selector },
	{ 0x0C0A, &host_GS_selector },
	{ 0x0C0C, &host_TR_selector },

	//--------------------
	// Guest-State fields
	//--------------------
	// Natural 64-bit Guest-State fields
	{ 0x6800, &guest_CR0 },
	{ 0x6802, &guest_CR3 },
	{ 0x6804, &guest_CR4 },
	{ 0x6806, &guest_ES_base },
	{ 0x6808, &guest_CS_base },
	{ 0x680A, &guest_SS_base },
	{ 0x680C, &guest_DS_base },
	{ 0x680E, &guest_FS_base },
	{ 0x6810, &guest_GS_base },
	{ 0x6812, &guest_LDTR_base },
	{ 0x6814, &guest_TR_base },
	{ 0x6816, &guest_GDTR_base },
	{ 0x6818, &guest_IDTR_base },
	{ 0x681A, &guest_DR7 },
	{ 0x681C, &guest_RSP },
	{ 0x681E, &guest_RIP },
	{ 0x6820, &guest_RFLAGS },
	{ 0x6822, &guest_pending_debug_x },
	{ 0x6824, &guest_SYSENTER_ESP },
	{ 0x6826, &guest_SYSENTER_EIP },



	// Natural 32-bit Guest-State fields
	{ 0x4800, &guest_ES_limit },
	{ 0x4802, &guest_CS_limit },
	{ 0x4804, &guest_SS_limit },
	{ 0x4806, &guest_DS_limit },
	{ 0x4808, &guest_FS_limit },
	{ 0x480A, &guest_GS_limit },
	{ 0x480C, &guest_LDTR_limit },
	{ 0x480E, &guest_TR_limit },
	{ 0x4810, &guest_GDTR_limit },
	{ 0x4812, &guest_IDTR_limit },
	{ 0x4814, &guest_ES_access_rights },
	{ 0x4816, &guest_CS_access_rights },
	{ 0x4818, &guest_SS_access_rights },
	{ 0x481A, &guest_DS_access_rights },
	{ 0x481C, &guest_FS_access_rights },
	{ 0x481E, &guest_GS_access_rights },
	{ 0x4820, &guest_LDTR_access_rights },
	{ 0x4822, &guest_TR_access_rights },
	{ 0x4824, &guest_interruptibility },
	{ 0x4826, &guest_activity_state },
	{ 0x4828, &guest_SMBASE },
	{ 0x482A, &guest_SYSENTER_CS },
	// Natural 16-bit Guest-State fields
	{ 0x0800, &guest_ES_selector },
	{ 0x0802, &guest_CS_selector },
	{ 0x0804, &guest_SS_selector },
	{ 0x0806, &guest_DS_selector },
	{ 0x0808, &guest_FS_selector },
	{ 0x080A, &guest_GS_selector },
	{ 0x080C, &guest_LDTR_selector },
	{ 0x080E, &guest_TR_selector },
	// Full 64-bit Guest-State fields
	{ 0x2800, &guest_VMCS_link_pointer_full },
	{ 0x2801, &guest_VMCS_link_pointer_high },
	{ 0x2802, &guest_IA32_DEBUGCTL_full },
	{ 0x2803, &guest_IA32_DEBUGCTL_high } };

const long elements = ( sizeof( machine ) ) / sizeof( VMCS_DEF );


VMCS_DEF  results[ ] = {
	{ 0x681C, &guest_RSP },
	{ 0x681E, &guest_RIP },
	{ 0x6820, &guest_RFLAGS },
	{ 0x0800, &guest_ES_selector },
	{ 0x0802, &guest_CS_selector },
	{ 0x0804, &guest_SS_selector },
	{ 0x0806, &guest_DS_selector },
	{ 0x0808, &guest_FS_selector },
	{ 0x080A, &guest_GS_selector },
	{ 0x080C, &guest_LDTR_selector },
	{ 0x080E, &guest_TR_selector },
	{ 0x4400, &info_vminstr_error }, 
	{ 0x4402, &info_vmexit_reason },
	{ 0x4404, &info_vmexit_interrupt_information },
	{ 0x4406, &info_vmexit_interrupt_error_code },
	{ 0x4408, &info_IDT_vectoring_information },
	{ 0x440A, &info_IDT_vectoring_error_code },
	{ 0x440C, &info_vmexit_instruction_length },
	{ 0x440E, &info_vmx_instruction_information },
	{ 0x6400, &info_exit_qualification },
	{ 0x6402, &info_IO_RCX },
	{ 0x6404, &info_IO_RSI },
	{ 0x6406, &info_IO_RDI },
	{ 0x6408, &info_IO_RIP },
	{ 0x640A, &info_guest_linear_address } };

const long rocount = sizeof( results ) / sizeof( VMCS_DEF );


//------------------------------------------------------------------------------
//
//
void islayer_clear_ioport_intercept(u32 port){
  u32 byte_offset, bit_offset;
	u8 *bit_vector = (u8 *)__vmx_io_bitmap;
  
	byte_offset = port / 8;
  bit_offset = port & 7;
  bit_vector[byte_offset] &= !(1 << bit_offset);
  
	return;
}

void islayer_set_ioport_intercept(u32 port){
  u32 byte_offset, bit_offset;
	u8 *bit_vector = (u8 *)__vmx_io_bitmap;
  
	byte_offset = port / 8;
  bit_offset = port & 7;
  bit_vector[byte_offset] |= (1 << bit_offset);
  
	return;
}

//------------------------------------------------------------------------------

// reboot helper
void islayer_reboot(void){
	//step-1: shut VMX off, else CPU ignores INIT signal!
	__asm__ __volatile__("vmxoff \r\n");
	write_cr4(read_cr4() & ~(CR4_VMXE));
	
	//step-2: zero out IDT
	{
		extern u32 __runtimeidt_start[];
		memset((void *)__runtimeidt_start, 0, PAGE_SIZE_4K);
	}
	
	//step-3: execute ud2 instruction to generate triple fault
	__asm__ __volatile__("ud2 \r\n");
	
	//never get here
	printf("\n%s: should never get here. halt!", __FUNCTION__);
	HALT();
}
