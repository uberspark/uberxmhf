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

//AMD SVM definitions
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __SVM_H__
#define __SVM_H__

#define SKINIT_SLB_SIZE 				0x10000

#define SIZEOF_MSRPM_BITMAP   			(2*4096)

#ifndef __ASSEMBLY__

//AMD SVM Exception Intercepts 
//each exception (0-31) is a bit, if set to 1 then the
//exception is intercepted
#define	EXCEPTION_INTERCEPT_DB 	(1UL << 1)

//SVM Class-1 and Class-2 Intercepts
//Appendix B-1, AMD SDM

//Class-1
#define SVM_CLASS1_INTERCEPT_NMI           (1UL << 1)
#define SVM_CLASS1_INTERCEPT_IOIO_PROT     (1UL << 27)
#define SVM_CLASS1_INTERCEPT_MSR_PROT      (1UL << 28)

//Class-2
#define SVM_CLASS2_INTERCEPT_VMRUN   		(1UL << 0)
#define SVM_CLASS2_INTERCEPT_VMMCALL 		(1UL << 1)
#define SVM_CLASS2_INTERCEPT_VMLOAD  		(1UL << 2)
#define SVM_CLASS2_INTERCEPT_VMSAVE  		(1UL << 3)
#define SVM_CLASS2_INTERCEPT_STGI    		(1UL << 4)
#define SVM_CLASS2_INTERCEPT_CLGI    		(1UL << 5)
#define SVM_CLASS2_INTERCEPT_SKINIT  		(1UL << 6)
#define SVM_CLASS2_INTERCEPT_ICEBP   		(1UL << 8)


//SVM VMEXIT Codes
//Appendix C AMD SDM
#define  SVM_VMEXIT_EXCEPTION_DB  		65
#define  SVM_VMEXIT_EXCEPTION_NMI 		66
#define	 SVM_VMEXIT_NMI                 97
#define  SVM_VMEXIT_INIT                99
#define  SVM_VMEXIT_IOIO             	123
#define	 SVM_VMEXIT_MSR                124
#define  SVM_VMEXIT_SHUTDOWN         	127
#define  SVM_VMEXIT_VMMCALL          	129
#define  SVM_VMEXIT_NPF              	1024
#define  SVM_VMEXIT_INVALID          	-1

//SVM VMCB TLB Control
//Appendix B-1 AMD SDM
#define	VMCB_TLB_CONTROL_NOTHING 				0
#define VMCB_TLB_CONTROL_FLUSHALL 				1
#define VMCB_TLB_CONTROL_THISGUEST				3
#define VMCB_TLB_CONTROL_THISGUESTNONGLOBAL		7

//SVM Nested Page Fault Error Codes
//Sec. 15.25.6 AMD SDM
#define VMCB_NPT_ERRORCODE_P		   	(1UL << 0)
#define VMCB_NPT_ERRORCODE_RW	     	(1UL << 1)
#define VMCB_NPT_ERRORCODE_US	      	(1UL << 2)
#define VMCB_NPT_ERRORCODE_RSV       	(1UL << 3)
#define VMCB_NPT_ERRORCODE_ID  			(1UL << 4)
#define VMCB_NPT_ERRORCODE_TABLEWALK 	(((u64)1)<<33)
#define VMCB_NPT_ERRORCODE_FINALWALK 	(((u64)1)<<32)

//SVM (Segment) Descriptor State Structure
//Appendix B-1 AMD SDM 
struct svmdesc {
  u16        selector;
  u16 		 attrib;
  u32        limit;
  u64        base;
} __attribute__ ((packed));


//SVM Event Injection Structure and Event Types
//Sec. 15.20 AMD SDM
struct svmeventinj {
    u64 vector:      8;
    u64 type:        3;
    u64 ev:     	 1;
    u64 reserved:   19;
    u64 v:           1;
    u64 errorcode:  32;
} __attribute__ ((packed));

#define EVENTINJ_TYPE_INTR			0
#define EVENTINJ_TYPE_NMI 			2
#define EVENTINJ_TYPE_EXCEPTION 	3
#define EVENTINJ_TYPE_SWINT 		4

//SVM I/O Intercept Information Structure
//Sec. 15.10.2, AMD SDM
union svmioiointerceptinfo {
    u64 rawbits;
    struct {
		u64 type: 1;
		u64 rsv0: 1;
		u64 str:  1;
		u64 rep:  1;
		u64 sz8:  1;
		u64 sz16: 1;
		u64 sz32: 1;
		u64 a16:  1;
		u64 a32:  1;
		u64 a64:  1;
		u64 seg:  3;
		u64 rsv1: 3;
		u64 port: 16;
	} __attribute__ ((packed)) fields;
} __attribute__ ((packed));

//SVM Virtual Machine Control Block Structure
//Appendix B-1, AMD SDM
struct _svm_vmcbfields {
  u8 __currently_unused0[8];          						
  u32 exception_intercepts_bitmask;   				//byte offset 0x08
  u32 class1_intercepts_bitmask;    				//byte offset 0x0C 
  u32 class2_intercepts_bitmask;					//byte offset 0x10 
  u8 __reserved0[44];						
  u64 iopm_base_pa;           						//byte offset 0x40
  u64 msrpm_base_pa;          						//byte offset 0x48 
  u8 __currently_unused1[8];		
  u32 guest_asid;             						//byte offset 0x58 
  u8  tlb_control;            						//byte offset 0x5C 
  u8 __reserved1[3];
  u8 __currently_unused2[16];
  u64 exitcode;               						//byte offset 0x70
  u64 exitinfo1;              						//byte offset 0x78 
  u64 exitinfo2;              						//byte offset 0x80 
  struct svmeventinj exitintinfo;    				//byte offset 0x88 
  u64 np_enable;              						//byte offset 0x90
  u8 __reserved2[16];
  struct svmeventinj eventinj;       				//byte offset 0xA8
  u64 n_cr3;                  						//byte offset 0xB0
  u8 __reserved3[840];             					
  struct svmdesc es;      							//byte offset 0x400
  struct svmdesc cs;
  struct svmdesc ss;
  struct svmdesc ds;
  struct svmdesc fs;
  struct svmdesc gs;
  struct svmdesc gdtr;
  struct svmdesc ldtr;
  struct svmdesc idtr;
  struct svmdesc tr;
  u8 __reserved4[43];
  u8 cpl;
  u8 __reserved5[4];
  u64 efer;                   						
  u8 __reserved6[112];
  u64 cr4;                    						
  u64 cr3;
  u64 cr0;
  u64 dr7;
  u64 dr6;
  u64 rflags;
  u64 rip;
  u8 __reserved7[88];
  u64 rsp;
  u8 __reserved8[24];
  u64 rax;
  u8 __currently_unused3[64];
  u64 cr2;
  u8 __currently_unused4[32];
  u64 g_pat;
  u8 __reserved9[2448];
} __attribute__ ((packed));

//macros for saving and storing additional VMCB state information
static inline void vmsave(u32 vmcb){
  __asm__("vmsave"
          :  // no output
          :"a"(vmcb));
}

static inline void vmload(u32 vmcb){
  __asm__("vmload"
          :  // no output
          :"a"(vmcb));
}

#endif /* __ASSEMBLY__ */

#endif /* __SVM_H__ */
