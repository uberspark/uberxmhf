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

//vmx.h - Intel VMX definitions
//author: amit vasudevan (amitvasudevan@acm.org)

#define VMXON_SIZE		(4096) 
#define VMCS_SIZE			(8192) 

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
#define INTR_TYPE_NMI										 (2UL << 8)	// NMI
#define INTR_TYPE_HW_EXCEPTION           (3UL << 8) // processor exception 
#define INTR_TYPE_SW_INTERRUPT         	 (4UL << 8) // software interrupt
#define INTR_TYPE_SW_EXCEPTION           (6UL << 8) // software exception (INTO, INT3)

//
#define VMX_EVENT_CANCEL  (0)
#define VMX_EVENT_INJECT  (1)

//
#define DF_VECTOR 	8
#define NMI_VECTOR	0x2
#define GP_VECTOR 	13
#define PF_VECTOR 	14

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
#define VMEXIT_INIT   0x3
#define VMEXIT_EPT_VIOLATION  0x30
#define VMEXIT_TASKSWITCH	0x9

#define VMEXIT_EPT_VIOLATON	48
#define VMEXIT_EPT_MISCONFIGURATION 49

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


#ifndef __ASSEMBLY__

/*struct regs
{
  u32 eax;
  u32 ecx;
  u32 edx;
  u32 ebx;
  u32 esp;
  u32 ebp;
  u32 esi;
  u32 edi;
}__attribute__ ((packed));*/


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


/*enum PFErrorcode
{
  PF_ERRORCODE_PRESENT   = 1 << 0,
  PF_ERRORCODE_WRITE     = 1 << 1,
  PF_ERRORCODE_USER      = 1 << 2,
  PF_ERRORCODE_RSV       = 1 << 3,
  PF_ERRORCODE_INST      = 1 << 4,
};*/

enum EPTViolationCode
{
	EPT_ERRORCODE_READ	   = 1 << 0,
	EPT_ERRORCODE_WRITE	   = 1 << 1,
	EPT_ERRORCODE_EXEC	   = 1 << 2,
};

#define	EPT_PROT_READ		(1UL << 0)
#define EPT_PROT_WRITE	(1UL << 1)
#define EPT_PROT_EXEC		(1UL << 2)

enum {
	TASK_SWITCH_CALL = 0,
  TASK_SWITCH_IRET = 1,
  TASK_SWITCH_JMP = 2,
  TASK_SWITCH_GATE = 3,
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


/*typedef union segment_attributes {
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
} __attribute__ ((packed)) segment_attributes_t;*/


/*typedef struct segment_register {
  u16        sel;
  segment_attributes_t attr;
  u32        limit;
  u64        base;
} __attribute__ ((packed)) segment_register_t;*/

typedef struct msr_entry {
	u32 index;
	u32 reserved;
	u64 data;
} __attribute__((packed)) msr_entry_t;


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


//VMX functions 
static inline void __vmx_vmxon(u64 vmxonRegion){
  __asm__("vmxon %0\n\t"
	  : //no outputs
	  : "m"(vmxonRegion));
}

static inline u32 __vmx_vmwrite(u32 encoding, u32 value){
  u32 status;
  __asm__("vmwrite %%ebx, %%eax \r\n"
          "jbe 1f \r\n"
          "movl $1, %%edx \r\n"
          "jmp 2f \r\n"
          "1: movl $0, %%edx \r\n"
          "2: movl %%edx, %0"
	  : "=m"(status)
	  : "a"(encoding), "b"(value)
    : "%edx"
    );
	return status;
}

static inline void __vmx_vmread(u32 encoding, u32 *value){
  u32 eflags;
	__asm__ __volatile__("vmread %%eax, %%ebx\n\t"
	  : "=b"(*value)
	  : "a"(encoding));
}

static inline u32 __vmx_vmclear(u64 vmcs){
  u32 status;
  __asm__("vmclear %1			\r\n"
	   	"jbe	1f    		\r\n"
      "movl $1, %%eax \r\n"
      "jmp  2f  \r\n"
      "1: movl $0, %%eax \r\n"
      "2: movl %%eax, %0 \r\n" 
    : "=m" (status)
    : "m"(vmcs)
    : "%eax"     
  );
  return status;
}

static inline u32 __vmx_vmptrld(u64 vmcs){
  u32 status;
  __asm__("vmptrld %1			\r\n"
	   	"jbe	1f    		\r\n"
      "movl $1, %%eax \r\n"
      "jmp  2f  \r\n"
      "1: movl $0, %%eax \r\n"
      "2: movl %%eax, %0 \r\n" 
    : "=m" (status)
    : "m"(vmcs)
    : "%eax"     
  );
  return status;
}


#define ASM_VMX_INVVPID		  ".byte 0x66, 0x0f, 0x38, 0x81, 0x08"
#define VMX_VPID_EXTENT_SINGLE_CONTEXT		1
#define VMX_VPID_EXTENT_ALL_CONTEXT		2


static inline void __vmx_invvpid(int ext, u16 vpid, u32 gva)
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


#define ASM_VMX_INVEPT		  ".byte 0x66, 0x0f, 0x38, 0x80, 0x08"
#define VMX_EPT_SINGLE_CONTEXT		1
#define VMX_EPT_GLOBAL		2


static inline void __vmx_invept(int ext, u64 eptp, u64 gpa)
{
    struct {
	u64 eptp;
	u64 gpa;
    } operand = { eptp, gpa };

    asm volatile (ASM_VMX_INVEPT
		  /* CF==1 or ZF==1 --> rc = -1 */
		  "; ja 1f ; ud2 ; 1:\n"
		  : : "a"(&operand), "c"(ext) : "cc", "memory");
}


#endif




