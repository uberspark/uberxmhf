#ifndef __TARGET_H_
#define __TARGET_H_

//loader at 0x1E00000

//#define __TARGET_BASE	0xBE000000 //(VT_SUPERMICRO)
#define __TARGET_BASE 0x80000000 //(VT_VPROUSFF)
#define __RUNTIMESTACK_SIZE	0x4000
#define __LOADERSTACK_SIZE	0x4000
#define __RUNTIMETSS_SIZE		0x1000

#define __GUESTOSBOOTMODULE_BASE	0x20000
#define __GUESTOSBOOTMODULESUP1_BASE	0x7C00

#define __CS 0x0008 /* Selector for GDT entry 1. RPL 0 */
#define __DS 0x0010 /* Selector for GDT enry 0. RPL 0 */
#define __TRSEL 0x0018

#define __LIMBO_GDT_SIZE	0x2000
#define __LIMBO_TSS_SIZE	0x1000

#define __V86M_CR0_INITVAL	0x00000020	//real-mode, no paging


#define __LDN_MODE_TRUSTED	0x5A
#define __LDN_MODE_UNTRUSTED 0xAA

#define ENTRY(x)\
  .globl x;	\
  .align;	\
  x:
#define ALIGN .align 4, 0x00

#define LINUX_BOOT_CS	0x1020
#define LINUX_BOOT_DS	0x1000
#define LINUX_BOOT_SP	0x9000
#define LOADER_REAL_START 0x20000
/* these two entries define the code, data and stack segment selectors 
 * for used to switch into real-mode. the corresponding segment 
 * descriptors define 16-bit segments. see loader code in boot/boot.S 
 * for the GDT.
 */
#define __ENTRY_CS 0x0018 	/* Selector for GDT entry 3. RPL 0 */
#define __ENTRY_DS 0x0020 	/* Selector for GDT enry 4. RPL 0 */


#ifndef __ASSEMBLY__

u32 runtime_initVT(void);
void runtime_setup_host(void);
void runtime_setup_guest(void);
void runtime_launch_guest(void);
u32 isl_prepareVMCS(u32 currentstate, u32 nextstate);
void isl_handleintercept_exception_0D(u32 errorcode);
void isl_handleintercept_wrmsr(void);
void isl_handleintercept_rdmsr(void);

void handle_intercept_cr0access(u32 gpr, u32 tofrom);
void handle_intercept_cr3access(u32 gpr, u32 tofrom);
void handle_intercept_cr4access(u32 gpr, u32 tofrom);


extern u32 __runtimeidt_start[];
extern u32 __runtimeidt_functionpointers[];
extern u32 __runtimeidt[];
extern u32 __runtimetss[];
extern u32 __runtimegdt_start[];
extern u32 __runtime_pdpt[];
extern u32 __runtime_pdts[];
extern u32 __runtime_reachregion[];
extern u32 runtime_stack[];
extern u32 __islayer_callback[];

extern u32 __runtime_v86_pagedir[];
extern u32 __runtime_v86_pagetables[];
extern u32 __runtime_v86_idt[];
extern u32 __runtime_v86_gdt[];
extern u32 __runtime_v86_tss[];
extern u32 __runtime_v86_ldt[];
extern u32 __runtime_v86_ring0stack[];


		extern u32 __v86_gpfh_stub[];
		extern u32 __v86_int10_stub[];
		extern u32 __runtime_v86_idtfunctionptrs[];

//guest state variables and defines
extern u32 guest_currentstate;
extern u32 guest_nextstate;

#define	GSTATE_DEAD									(0)
#define GSTATE_REALMODE							(1UL << 0)
#define GSTATE_PROTECTEDMODE				(1UL << 1)
#define GSTATE_PROTECTEDMODE_TR			(1UL << 2)
#define GSTATE_PROTECTEDMODE_GDTR		(1UL << 3)
#define GSTATE_PROTECTEDMODE_IDTR		(1UL << 4)
#define GSTATE_PROTECTEDMODE_PG			(1UL << 5)

//v86 monitor variables
extern u32 v86monitor_guest_gdt_base;
extern u16 v86monitor_guest_gdt_limit;
extern u32 v86monitor_guest_idt_base;
extern u16 v86monitor_guest_idt_limit;
extern u32 v86monitor_guest_reg_cr0; //ET=1, 387+ FPU

extern u32 v86monitor_guest_reg_eax;
extern u32 v86monitor_guest_reg_ebx;
extern u32 v86monitor_guest_reg_ecx;
extern u32 v86monitor_guest_reg_edx;
extern u32 v86monitor_guest_reg_esi;
extern u32 v86monitor_guest_reg_edi;
extern u32 v86monitor_guest_reg_ebp;
extern u32 v86monitor_guest_reg_esp;
extern u32 v86monitor_guest_reg_eip;
extern u32 v86monitor_guest_reg_cs;
extern u32 v86monitor_guest_reg_ss;
extern u32 v86monitor_guest_reg_eflags;
extern u32 v86monitor_guest_reg_cr4;
extern u32 v86monitor_guest_reg_cr3;

//
extern u32 isl_guesthastr;
extern u32 isl_guest_TR_base;
extern u32 isl_guest_TR_access_rights;
extern u32 isl_guest_TR_limit;
extern u16 isl_guest_TR_selector;

//
extern u32 __limbo_gdt[];
extern u32 __limbo_tss[];
extern u32 limbo_rsp;

//#define __pa(x) x
//#define __gpa2hva(x) x

typedef struct {
	u32 XtVmmEntryPoint;
	u32 XtVmmPdptBase;
	u32 XtVmmPdtsBase;
	u32 XtGuestOSBootModuleBase;
	u32 XtGuestOSBootModuleSize;
	u32 XtGuestOSBootModuleBaseSup1;
	u32 XtGuestOSBootModuleSizeSup1;
	u32 XtVmmStackBase;
	u32 XtVmmStackSize;
	u32 XtVmmGdt;
	u32 XtVmmIdt;
	u32 XtVmmIdtFunctionPointers;
	u32 XtVmmIdtEntries;
	u32 XtVmmVMXONBase;
	u32 XtVmmVMCSBase;
} __attribute__((packed)) XTLPB, *PXTLPB;

extern PXTLPB	lpb;

//#define HALT()	__asm__ __volatile__ ("hlt\r\n");

#endif

#endif /* __TARGET_H_ */
