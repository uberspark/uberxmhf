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

//xmhf.h - main XMHF core header file
// this orchestrates the inclusion of other core component specific
// headers
//author: amit vasudevan (amitvasudevan@acm.org)
//
#ifndef __XC_H_
#define __XC_H_


#ifndef __ASSEMBLY__
	#include <xmhfcrypto.h>
#endif // __ASSEMBLY__


//arch. specific stuff
#define XC_HYPAPP_ARCH_PARAM_OPERATION_CBTRAP_IO		(0x101)



#define XC_HYPAPP_ARCH_PARAM_OPERATION_TRAP_IO			(0xC01)


#define XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CPUGPRS		(0xD01)
#define XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_DESC		(0xD02)
#define XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_ACTIVITY	(0xD03)
#define XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_CONTROLREGS	(0xD04)
#define XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_INFOREGS	(0xD05)
#define XC_HYPAPP_ARCH_PARAM_OPERATION_CPUSTATE_SYSENTER	(0xD06)



#ifndef __ASSEMBLY__


typedef struct {
	u32 portnum;
	u32 access_type;
	u32 access_size;
} xc_hypapp_arch_param_x86vmx_cbtrapio_t;

typedef struct {
	u32 portnum;
	u32 access_size;
} xc_hypapp_arch_param_x86vmx_trapio_t;

typedef struct {
	x86desc_t cs;
	x86desc_t ds;
	x86desc_t es;
	x86desc_t fs;
	x86desc_t gs;
	x86desc_t ss;
	x86desc_t idtr;
	x86desc_t ldtr;
	x86desc_t gdtr;
	x86desc_t tr;
} xc_hypapp_arch_param_x86vmx_cpustate_desc_t;

typedef struct {
	u64 rip;
	u64 rflags;
	u32 activity_state;
	u32 interruptibility;
} xc_hypapp_arch_param_x86vmx_cpustate_activity_t;

typedef struct {
	u64 cr0;
	u64 control_cr0_shadow;
	u64 cr3;
	u64 cr4;
} xc_hypapp_arch_param_x86vmx_cpustate_controlregs_t;

typedef struct {
	u32 sysenter_cs;
	u64 sysenter_rsp;
	u64 sysenter_rip;
} xc_hypapp_arch_param_x86vmx_cpustate_sysenter_t;

typedef struct {
  u32  info_vminstr_error;
  u32  info_vmexit_reason;
  u32  info_vmexit_interrupt_information;
  u32  info_vmexit_interrupt_error_code;
  u32  info_idt_vectoring_information;
  u32  info_idt_vectoring_error_code;
  u32  info_vmexit_instruction_length;
  u32  info_vmx_instruction_information;
  u64  info_exit_qualification;
  u64  info_io_rcx;
  u64  info_io_rsi;
  u64  info_io_rdi;
  u64  info_io_rip;
  u64  info_guest_linear_address;
  u64  info_guest_paddr_full;
} xc_hypapp_arch_param_x86vmx_cpustate_inforegs_t;


typedef struct {
	u32 operation;
	union {
		struct regs cpugprs;
		xc_hypapp_arch_param_x86vmx_cbtrapio_t cbtrapio;
		xc_hypapp_arch_param_x86vmx_trapio_t trapio;
		xc_hypapp_arch_param_x86vmx_cpustate_desc_t desc;
		xc_hypapp_arch_param_x86vmx_cpustate_activity_t activity;
		xc_hypapp_arch_param_x86vmx_cpustate_controlregs_t controlregs;
		xc_hypapp_arch_param_x86vmx_cpustate_inforegs_t inforegs;
		xc_hypapp_arch_param_x86vmx_cpustate_sysenter_t sysenter;
	} param;
} __attribute__ ((packed)) xc_hypapp_arch_param_t;

#endif //__ASSEMBLY__


#define XC_HYPAPPCB_CHAIN                       (1)
#define XC_HYPAPPCB_NOCHAIN                     (2)

#define XC_HYPAPPCB_INITIALIZE                  (1)
#define XC_HYPAPPCB_HYPERCALL                   (2)
#define XC_HYPAPPCB_MEMORYFAULT                 (3)
#define XC_HYPAPPCB_SHUTDOWN                    (4)
#define XC_HYPAPPCB_TRAP_IO                     (5)
#define XC_HYPAPPCB_TRAP_INSTRUCTION            (6)
#define XC_HYPAPPCB_TRAP_EXCEPTION              (7)


#define XC_HYPAPPCB_TRAP_INSTRUCTION_CPUID      (0x60)
#define XC_HYPAPPCB_TRAP_INSTRUCTION_WRMSR      (0x61)
#define XC_HYPAPPCB_TRAP_INSTRUCTION_RDMSR      (0x62)


typedef struct {
    u32 cbtype;
    u32 cbqual;
    u32 guest_slab_index;
}__attribute__((packed)) xc_hypappcb_inputparams_t;


typedef struct {
    u32 cbresult;
}__attribute__((packed)) xc_hypappcb_outputparams_t;


typedef struct {
    u32 cbtype;
    u32 cbqual;
    u32 guest_slab_index;
    u32 cbresult;
}__attribute__((packed)) xc_hypappcb_params_t;

typedef struct {
    u32 xmhfhic_slab_index;
    u32 cbmask;
} __attribute__((packed)) xc_hypapp_info_t;


#define XC_HYPAPPCB_MASK(x) (1 << x)

static xc_hypapp_info_t _xcihub_hypapp_info_table[] = {
/*    {
        XMHF_HYP_SLAB_XHHYPERDEP,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_MEMORYFAULT) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },

    {
        XMHF_HYP_SLAB_XHAPPROVEXEC,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_MEMORYFAULT) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },


    {
        XMHF_HYP_SLAB_XHSSTEPTRACE,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_TRAP_EXCEPTION) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },
*/
    {
        XMHF_HYP_SLAB_XHSYSCALLLOG,
        (XC_HYPAPPCB_MASK(XC_HYPAPPCB_HYPERCALL) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_MEMORYFAULT) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_TRAP_INSTRUCTION) | XC_HYPAPPCB_MASK(XC_HYPAPPCB_SHUTDOWN) )
    },

};

#define HYPAPP_INFO_TABLE_NUMENTRIES (sizeof(_xcihub_hypapp_info_table)/sizeof(_xcihub_hypapp_info_table[0]))


/*
x86_64
static inline u64 xc_hcbinvoke(u64 cbtype, u64 cbqual, u64 guest_slab_index){
    u64 status = XC_HYPAPPCB_CHAIN;
    u64 i;
    xc_hypappcb_inputparams_t hcb_iparams;
    xc_hypappcb_outputparams_t hcb_oparams;

    hcb_iparams.cbtype = cbtype;
    hcb_iparams.cbqual = cbqual;
    hcb_iparams.guest_slab_index = guest_slab_index;

    for(i=0; i < HYPAPP_INFO_TABLE_NUMENTRIES; i++){
        if(_xcihub_hypapp_info_table[i].cbmask & XC_HYPAPPCB_MASK(cbtype)){
            XMHF_SLAB_CALL(hypapp, _xcihub_hypapp_info_table[i].xmhfhic_slab_index, &hcb_iparams, sizeof(hcb_iparams), &hcb_oparams, sizeof(hcb_oparams));
            if(hcb_oparams.cbresult == XC_HYPAPPCB_NOCHAIN){
                status = XC_HYPAPPCB_NOCHAIN;
                break;
            }
        }
    }

    return status;
}
*/

static inline u32 xc_hcbinvoke(u32 src_slabid, u32 cpuid, u32 cbtype, u32 cbqual, u32 guest_slab_index){
    u32 status = XC_HYPAPPCB_CHAIN;
    u32 i;
    slab_params_t spl;
    xc_hypappcb_params_t *hcbp = (xc_hypappcb_params_t *)&spl.in_out_params[0];

    spl.src_slabid = src_slabid;
    spl.cpuid = cpuid;
    hcbp->cbtype=cbtype;
    hcbp->cbqual=cbqual;
    hcbp->guest_slab_index=guest_slab_index;

    for(i=0; i < HYPAPP_INFO_TABLE_NUMENTRIES; i++){
        if(_xcihub_hypapp_info_table[i].cbmask & XC_HYPAPPCB_MASK(cbtype)){
            spl.dst_slabid = _xcihub_hypapp_info_table[i].xmhfhic_slab_index;
            XMHF_SLAB_CALLNEW(&spl);
            if(hcbp->cbresult == XC_HYPAPPCB_NOCHAIN){
                status = XC_HYPAPPCB_NOCHAIN;
                break;
            }
        }
    }

    return status;
}



#endif /* __XC_H_ */
