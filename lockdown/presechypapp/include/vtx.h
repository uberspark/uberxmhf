#define GETSEC_SLB_SIZE	0x10000

#define VMXON_SIZE	4096 
#define VMCS_SIZE	8192 

//VM Exit Interruption-information format
#define INTR_INFO_VECTOR_MASK           (0x000000ff)        // 7:0 
#define INTR_INFO_INTR_TYPE_MASK        (0x00000700)        // 10:8 
#define INTR_INFO_DELIVER_CODE_MASK     (0x00000800)        // 11 
#define INTR_INFO_VALID_MASK            (0x80000000)      	// 31 

#define VECTORING_INFO_VECTOR_MASK           	INTR_INFO_VECTOR_MASK
#define VECTORING_INFO_TYPE_MASK        			INTR_INFO_INTR_TYPE_MASK
#define VECTORING_INFO_DELIVER_CODE_MASK    	INTR_INFO_DELIVER_CODE_MASK
#define VECTORING_INFO_VALID_MASK       			INTR_INFO_VALID_MASK

#define INTR_TYPE_HW_INTERRUPT         	 (0UL << 8) // hardware/external interrupt 
#define INTR_TYPE_HW_EXCEPTION           (3UL << 8) // processor exception 
#define INTR_TYPE_SW_INTERRUPT         	 (4UL << 8) // software interrupt
#define INTR_TYPE_SW_EXCEPTION           (6UL << 8) // software exception (INTO, INT3)


//
#define VMX_EVENT_CANCEL  (0)
#define VMX_EVENT_INJECT  (1)

//
#define DF_VECTOR 8
#define GP_VECTOR 13
#define PF_VECTOR 14


#ifndef __ASSEMBLY__

struct regs
{
  u32 eax;
  u32 ecx;
  u32 edx;
  u32 ebx;
  u32 esp;
  u32 ebp;
  u32 esi;
  u32 edi;
};

extern u32 vm_cr2;
extern u32 vm_eax, vm_ebx, vm_ecx, vm_edx;
extern u32 vm_esi, vm_edi, vm_ebp;




#define INTERCEPT_EXCEPTIONS_00 (0x00)
#define INTERCEPT_EXCEPTIONS_01 (0x01)
#define INTERCEPT_EXCEPTIONS_02 (0x02)
#define INTERCEPT_EXCEPTIONS_03 (0x03)
#define INTERCEPT_EXCEPTIONS_04 (0x04)
#define INTERCEPT_EXCEPTIONS_05 (0x05)
#define INTERCEPT_EXCEPTIONS_06 (0x06)
#define INTERCEPT_EXCEPTIONS_07 (0x07)
#define INTERCEPT_EXCEPTIONS_08 (0x08)
#define INTERCEPT_EXCEPTIONS_09 (0x09)
#define INTERCEPT_EXCEPTIONS_0A (0x0A)
#define INTERCEPT_EXCEPTIONS_0B (0x0B)
#define INTERCEPT_EXCEPTIONS_0C (0x0C)
#define INTERCEPT_EXCEPTIONS_0D (0x0D)
#define INTERCEPT_EXCEPTIONS_0E (0x0E)
#define INTERCEPT_EXCEPTIONS_0F (0x0F)
#define INTERCEPT_EXCEPTIONS_10 (0x10)
#define INTERCEPT_EXCEPTIONS_11 (0x11)
#define INTERCEPT_EXCEPTIONS_12 (0x12)
#define INTERCEPT_EXCEPTIONS_13 (0x13)
#define INTERCEPT_EXCEPTIONS_14 (0x14)
#define INTERCEPT_EXCEPTIONS_15 (0x15)
#define INTERCEPT_EXCEPTIONS_16 (0x16)
#define INTERCEPT_EXCEPTIONS_17 (0x17)
#define INTERCEPT_EXCEPTIONS_18 (0x18)
#define INTERCEPT_EXCEPTIONS_19 (0x19)
#define INTERCEPT_EXCEPTIONS_1A (0x1A)
#define INTERCEPT_EXCEPTIONS_1B (0x1B)
#define INTERCEPT_EXCEPTIONS_1C (0x1C)
#define INTERCEPT_EXCEPTIONS_1D (0x1D)
#define INTERCEPT_EXCEPTIONS_1E (0x1E)
#define INTERCEPT_EXCEPTIONS_1F (0x1F)
#define INTERCEPT_EXCEPTIONS_20 (0x20)
        

#define INTERCEPT_INVLPG          0x21
#define INTERCEPT_CR3_READ        0x22
#define INTERCEPT_CR3_WRITE       0x23
#define INTERCEPT_CR0_SEL_WRITE   0x24
#define INTERCEPT_CR4_WRITE       0x25
#define INTERCEPT_MSR             0x26
#define INTERCEPT_IOIO            0x27
#define INTERCEPT_VMMCALL         0x28
#define INTERCEPT_EXCEPTIONS      0x29

#define VMEXIT_EXCEPTION  0x00
#define VMEXIT_INVLPG 14

#define VMEXIT_CRX_ACCESS 0x1C

#define VMX_CRX_ACCESS_FROM	0x1
#define VMX_CRX_ACCESS_TO		0x0

#define VMEXIT_CR3_READ 28
#define VMEXIT_CR3_WRITE  28
#define VMEXIT_CR0_SEL_WRITE 28
#define VMEXIT_CR4_WRITE 28
#define VMEXIT_CRX_READWRITE 28
#define VMEXIT_MSR_READ   31
#define VMEXIT_MSR_WRITE 32
#define VMEXIT_IOIO 30
#define VMEXIT_VMCALL 18
#define VMEXIT_HLT 12
#define VMEXIT_INVLPG 14	
#define VMEXIT_RDMSR	0x1f
#define VMEXIT_WRMSR	0x20
#define VMEXIT_CPUID	0x0a

//VMEXIT_IOIO defines
#define	IO_SIZE_BYTE	0x0
#define IO_SIZE_WORD	0x1
#define IO_SIZE_DWORD	0x3

#define IO_TYPE_IN		0x1
#define IO_TYPE_OUT		0x0

#define IO_INSN_STRING	0x1
#define IO_INSN_NORMAL	0x0
#define IO_INSN_REP			0x1
#define IO_INSN_OPCODE_IMM	0x1


void vtx_initvmx(void);
void vtx_initlinuxvmcs(void);
void vtx_vmexit(void);
void vtx_loadvmcs(void);
void vtx_storevmcs(void);
void vtx_dumpvmcs(void);

typedef struct {
  u32 writable;
  u32 encoding;
  u32 addressofvariable;
} __attribute__ ((packed)) VMCSENCODINGS;


typedef struct {
	u32 type: 4;
	u32 desctype: 1; //0=system, 1=code or data
	u32 dpl: 2;
	u32 p: 1;
	u32 res1: 4;
	u32 avl: 1;
	u32 csmode: 1;
	u32 s: 1; //0=16-bit segment, 1=32-bit segment
	u32 g: 1;
	u32 usable: 1; //0=usable, 1=unusable
	u32 res2: 15;
} __attribute__ ((packed)) segment_desc_accessrights;



enum PFErrorcode
{
  PF_ERRORCODE_PRESENT   = 1 << 0,
  PF_ERRORCODE_WRITE     = 1 << 1,
  PF_ERRORCODE_USER      = 1 << 2,
  PF_ERRORCODE_RSV       = 1 << 3,
  PF_ERRORCODE_INST      = 1 << 4,
};


typedef struct {
	u16 sel;		  
	u64 base;
	u32 limit;
	union{
		segment_desc_accessrights ar;
		u32 aru32;
	};
} __attribute__ ((packed)) segment_desc;


typedef union segment_attributes {
  u16 bytes;
  struct
  {
    u16 type:4;    /* 0;  Bit 40-43 */
    u16 s:   1;    /* 4;  Bit 44 */
    u16 dpl: 2;    /* 5;  Bit 45-46 */
    u16 p:   1;    /* 7;  Bit 47 */
    u16 avl: 1;    /* 8;  Bit 52 */
    u16 l:   1;    /* 9;  Bit 53 */
    u16 db:  1;    /* 10; Bit 54 */
    u16 g:   1;    /* 11; Bit 55 */
  } fields;
} __attribute__ ((packed)) segment_attributes_t;


typedef struct segment_register {
  u16        sel;
  segment_attributes_t attr;
  u32        limit;
  u64        base;
} __attribute__ ((packed)) segment_register_t;


//VMCS consists of 4 regions:
//control fields, guest-state fields, host-state fields and
//read-only data fields
typedef struct {
  //control fields
  u16 ctrl_vpid;

  u32 ctrl_pinbased;
  u32 ctrl_procbased;
  u32 ctrl_exceptionbitmap;
  u32 ctrl_pferrmask;
  u32 ctrl_pferrmatch;
  u32 ctrl_cr3targetcount;
  u32 ctrl_vmexit;
  u32 ctrl_vmexitmsrstorecount;
  u32 ctrl_vmexitmsrloadcount;
  u32 ctrl_vmentry;
  u32 ctrl_vmentrymsrloadcount;
  u32 ctrl_vmentryinterruptioninfo;
  u32 ctrl_vmentryexceptionerrorcode;
  u32 ctrl_vmentryinstructionlength;
  u32 ctrl_tprthreshold;
  u32 ctrl_secprocbased;

  u64 ctrl_addressiobitmapA;
  u32 ctrl_addressiobitmapAhigh;
  u64 ctrl_addressiobitmapB;
  u32 ctrl_addressiobitmapBhigh;
  u64 ctrl_addressmsrbitmaps;
  u32 ctrl_addressmsrbitmapshigh;
  u64 ctrl_vmexitmsrstoreaddress;
  u32 ctrl_vmexitmsrstoreaddresshigh;
  u64 ctrl_vmexitmsrloadaddress;
  u32 ctrl_vmexitmsrloadaddresshigh;
  u64 ctrl_vmentrymsrloadaddress;
  u32 ctrl_vmentrymsrloadaddresshigh;
  u64 ctrl_vmcsexecptr;
  u32 ctrl_vmcsexecptrhigh;
  u64 ctrl_tscoffset;
  u32 ctrl_tscoffsethigh;
  u64 ctrl_virtualapicaddress;
  u32 ctrl_virtualapicaddresshigh;
  u64 ctrl_apicaccessaddress;
  u32 ctrl_apicaccessaddresshigh;
	u64 ctrl_eptpointer;
	u32 ctrl_eptpointerhigh;
  
  u64 ctrl_cr0mask;
  u64 ctrl_cr4mask;
  u64 ctrl_cr0readshadow;
  u64 ctrl_cr4readshadow;
  u64 ctrl_cr3targetvalue0;
  u64 ctrl_cr3targetvalue1;
  u64 ctrl_cr3targetvalue2;
  u64 ctrl_cr3targetvalue3;
  
	//host-state fields
  segment_desc  h_es;
  segment_desc  h_cs;
  segment_desc  h_ss;
  segment_desc  h_ds;
  segment_desc  h_fs;
  segment_desc  h_gs;
  segment_desc  h_tr;
	segment_desc  h_gdtr;
	segment_desc  h_idtr;
	
  u32 h_ia32_sysenter_cs;

  u64 h_ia32_pat;
  u32 h_ia32_pathigh;
  u64 h_ia32_efer;
  u32 h_ia32_eferhigh;
  u64 h_ia32_perfglobalctrl;
  u32 h_ia32_perfglobalctrlhigh;

  u64 h_cr0;
  u64 h_cr3;
  u64 h_cr4;
  u32 h_ia32_sysenter_esp;
  u32 h_ia32_sysenter_eip;
  u64 h_rsp;
  u64 h_rip;
  
  //guest-state fields
  segment_desc  g_es;
  segment_desc  g_cs;
  segment_desc  g_ss;
  segment_desc  g_ds;
  segment_desc  g_fs;
  segment_desc  g_gs;
  segment_desc  g_ldtr;
  segment_desc  g_tr;
  segment_desc  g_gdtr;
  segment_desc  g_idtr;

  u32 g_interruptibility;
  u32 g_activitystate;
  u32 g_smbase;
	u32 g_ia32_sysenter_cs;
	u32 g_timer;	

  u64 g_vmcs_linkptr;
  u32 g_vmcs_linkptrhigh;
  u64 g_ia32_debugctl;
  u32 g_ia32_debugctlhigh;
	u64 g_ia32_pat;
	u32 g_ia32_pathigh;
	u64 g_ia32_efer;
	u32 g_ia32_eferhigh;
  u64 g_ia32_perfglobalctrl;
  u32 g_ia32_perfglobalctrlhigh;
	u64 g_ia32_pdpte0;
	u32 g_ia32_pdpte0high;
	u64 g_ia32_pdpte1;
	u32 g_ia32_pdpte1high;
	u64 g_ia32_pdpte2;
	u32 g_ia32_pdpte2high;
	u64 g_ia32_pdpte3;
	u32 g_ia32_pdpte3high;
		
  u64 g_cr0;
  u64 g_cr3;
  u64 g_cr4;
  u64 g_dr7;
  u64 g_rsp;
  u64 g_rip;
  u64 g_rflags;
  u64 g_sysenter_esp;
  u64 g_sysenter_eip;
  u64 g_pendingdebugexceptions;
  
	//read-only data fields	
  u32 data_vminstructionerror;
  u32 data_exitreason;
  u32 data_vmexitinterruptioninfo;
  u32 data_vmexitinterruptionerrorcode;
  u32 data_idtvectoringinfo;
  u32 data_idtvectoringerrorcode;
  u32 data_vmexitinstructionlength;
  u32 data_vmexitinstructioninfo;
  
	u64 data_guestphysicaladdress;
	u32 data_guestphysicaladdresshigh;
	 
  u64 data_exitqualification;
  u64 data_iorcx;
  u64 data_iorsi;
  u64 data_iordi;
  u64 data_iorip;
  u64 data_guestlinearaddress;
} __attribute__ ((packed)) VMCS;


typedef struct {
  u32 id;
  u32 vmxonSize;
  u32 physicalAddressWidth;
  u32 vmcsMemoryType;
  u32 ioCapability;
  u64 cr0fixed0;
  u64 cr0fixed1;
  u64 cr4fixed0;
  u64 cr4fixed1;
  u64 pinbasedctls;
  u64 procbasedctls;
  u64 procbasedctls2;
u64 exitctls;
u64 entryctls;
}__attribute__ ((packed)) VMXINFO;


//VMX 
static inline void VMXON(u64 vmxonRegion){
  __asm__("vmxon %0\n\t"
	  : //no outputs
	  : "m"(vmxonRegion));
}

static inline void VMWRITE(u32 encoding, u32 value){
  __asm__("vmwrite %%ebx, %%eax\n\t"
	  : //no outputs
	  : "a"(encoding), "b"(value));
}

static inline void VMREAD(u32 encoding, u32 *value){
  u32 eflags;
	__asm__ __volatile__("vmread %%eax, %%ebx\n\t"
	  : "=b"(*value)
	  : "a"(encoding));
	__asm__ __volatile__("pushfl\n\t"
											 "popl %0 \n\t"
		:"=g" (eflags)
		: /* no input */ 
		:"memory");
	if(eflags & (u32)0x00000001){
		printf("\nHALT: VMREAD error (flags=0x%08x), encoding=0x%08x", 
			eflags, encoding);
		__asm__ __volatile__("hlt \n\t");
	}
}


#endif

/*
#define ADDR_VMXONREGION  0xC2000000
#define ADDR_LINUXVMCS    0xC2100000
#define ADDR_LINUXVMCSREGION  0xC2200000


typedef struct {
  u32 id;
  u32 vmxonSize;
  u32 physicalAddressWidth;
  u32 vmcsMemoryType;
  u32 ioCapability;
  u64 cr0fixed0;
  u64 cr0fixed1;
  u64 cr4fixed0;
  u64 cr4fixed1;

}VMXINFO;


typedef union segment_attributes {
    u16 bytes;
    struct
    {
        u16 type:4;    // 0;  Bit 40-43 
        u16 s:   1;    // 4;  Bit 44 
        u16 dpl: 2;    // 5;  Bit 45-46 
        u16 p:   1;    // 7;  Bit 47 
        u16 avl: 1;    // 8;  Bit 52 
        u16 l:   1;    // 9;  Bit 53 
        u16 db:  1;    // 10; Bit 54 
        u16 g:   1;    // 11; Bit 55 
    } fields;
} __attribute__ ((packed)) segment_attributes_t;

typedef struct segment_register {
    u16        sel;
    segment_attributes_t attr;
    u32        limit;
    u64        base;
} __attribute__ ((packed)) segment_register_t;



enum VM_INTERCEPTS {
  EXCEPTION_INTERCEPT_GP = 1 << 13,
  EXCEPTION_INTERCEPT_PF = 1 << 14,
  
  CR_INTERCEPT_CR0_READ = 1 << 0 ,
  CR_INTERCEPT_CR0_WRITE = 1 << 1 ,
  CR_INTERCEPT_CR3_READ = 1 << 2 ,
  CR_INTERCEPT_CR3_WRITE = 1 << 3 ,
  GENERAL1_INTERCEPT_CR0_SEL_WRITE = 1 << 4 ,
  GENERAL1_INTERCEPT_INVLPG = 1 << 5 ,
  GENERAL1_INTERCEPT_MSR_READ = 1 << 6,
  GENERAL1_INTERCEPT_MSR_WRITE = 1 << 7,
  GENERAL1_INTERCEPT_IOIO_PROT = 1 << 8
};

enum VM_OPT {
  OFF = 0;
  ON = 1;
};

enum VMEXIT_EXITCODE
{
    VMEXIT_CR_ACCESS = 28,
    VMEXIT_INVLPG = 14,
    VMEXIT_VMMCALL = 18,
    VMEXIT_MSR_READ = 31,
    VMEXIT_MSR_WRITE = 32,
    VMEXIT_IOIO = 30,
};

typedef struct vmcs_struct {

  //guest state    
  segment_register_t es;      
  segment_register_t cs;
  segment_register_t ss;
  segment_register_t ds;
  segment_register_t fs;
  segment_register_t gs;
  segment_register_t gdtr;
  segment_register_t ldtr;
  segment_register_t idtr;
  segment_register_t tr;
    
  u8 cpl;
    
  u64 cr0;
  u64 cr2;
  u64 cr3;
  u64 cr4;                    
  
  u64 rip;
  u64 rsp;
  u64 rflags;
    
  u64 sysenter_cs;
  u64 sysenter_esp;
  u64 sysenter_eip;
    
    
  //host state (VMM)
  segment_register_t h_es;      
  segment_register_t h_cs;
  segment_register_t h_ss;
  segment_register_t h_ds;
  segment_register_t h_fs;
  segment_register_t h_gs;
  segment_register_t h_gdtr;
  segment_register_t h_ldtr;
  segment_register_t h_idtr;
  segment_register_t h_tr;

  u64 h_cr0;
  u64 h_cr3;
  u64 h_cr4;
  
  u64 h_rip;
  u64 h_rsp;
  
  u64 h_sysenter_cs;
  u64 h_sysenter_esp;
  u64 h_sysenter_eip;
    
  //control state
  u32 exitcode;
  u64 exitqualification;
    
  u32 procctl;
  u32 exceptionbitmap;
    
  u64 iopm_base_pa;           
  u64 msrpm_base_pa;          
  u64 tsc_offset;             


} __attribute__ ((packed)) VMCS;

//VMX 
static inline void VMXON(u64 *vmxonRegion){
  __asm__("vmxon %0\n\t"
	  : //no outputs
	  : "m"(vmxonRegion));
}

static inline void VMXREAD(u32 encoding, u32 *value){
  __asm__("vmread %%eax, %%ebx\n\t"
	  : "=b"(*value)
	  : "a"(encoding)
    : "%eax", "%ebx");
}

static inline void VMXWRITE(u32 encoding, u32 value){
  __asm__("vmwrite %%ebx, %%eax\n\t"
	  : //no outputs
	  : "a"(encoding), "b"(value)
    : "%eax", "%ebx");
}

static inline void VMCLEAR(u64 vmcs){
  __asm__("vmclear %0\n\t"
	  : //no outputs
	  : "m"(vmcs));
}

static inline void VMPTRLD(u64 vmcs){
  __asm__("vmclear %0\n\t"
	  : //no outputs
	  : "m"(vmcs));
}
*/

#define ASM_VMX_INVVPID		  ".byte 0x66, 0x0f, 0x38, 0x81, 0x08"
#define VMX_VPID_EXTENT_SINGLE_CONTEXT		1
#define VMX_VPID_EXTENT_ALL_CONTEXT		2

static inline void __invvpid(int ext, u16 vpid, u32 gva)
{
    struct {
	u64 vpid : 16;
	u64 rsvd : 48;
	u64 gva;
    } operand = { vpid, 0, gva };

    asm volatile (ASM_VMX_INVVPID
		  /* CF==1 or ZF==1 --> rc = -1 */
		  "; ja 1f ; ud2 ; 1:"
		  : : "a"(&operand), "c"(ext) : "cc", "memory");
}
