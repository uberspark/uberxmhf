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

// XMHF slab decls./defns.
// author: amit vasudevan (amitvasudevan@acm.org)
// XXX: need to split arch. dependent portions

#ifndef __XMHF_HIC_H__
#define __XMHF_HIC_H__


#define XMHF_HIC_HYP_SLABS_COUNT            (1)
#define XMHF_HIC_GUEST_SLABS_COUNT          (1)


#define XMHF_HYP_SLAB_HICTESTSLAB1          (0)





//#define XMHF_SLAB_CALLP2P					0xB0

#define XMHF_SLAB_CALLTYPE_CALLP2P				0xB0
#define XMHF_SLAB_CALLTYPE_RETP2P               0xB1


#define XMHF_SLAB_XCPRIMEON_INDEX			(0)
#define XMHF_SLAB_TESTSLAB1_INDEX			(1)
#define XMHF_SLAB_TESTSLAB2_INDEX			(2)
#define XMHF_SLAB_XCEXHUB_INDEX				(3)
#define XMHF_SLAB_XCSMP_INDEX				(4)
#define XMHF_SLAB_XCDEV_INDEX               (5)
#define XMHF_SLAB_XCRICHGUEST_INDEX			(6)
#define XMHF_SLAB_XCIHUB_INDEX				(7)

#define XMHF_SLAB_XCAPIPLATFORM_INDEX       (8)
#define XMHF_SLAB_XCAPIHPT_INDEX            (9)
#define XMHF_SLAB_XCAPICPUSTATE_INDEX       (10)
#define XMHF_SLAB_XCAPITRAPMASK_INDEX       (11)
#define XMHF_SLAB_XCAPIPARTITION_INDEX      (12)

#define XMHF_SLAB_XCAPI_INDEX               (13)

//hypapp slab indices currently allow for only one hypapp to be linked in
//TODO: add support for multiple hypapps
#define XMHF_SLAB_XHHYPERDEP_INDEX			(13)
#define XMHF_SLAB_XHHELLOWORLD_INDEX		(13)

#ifndef __ASSEMBLY__
typedef void slab_input_params_t;
typedef void slab_output_params_t;



void xmhfhic_arch_sanity_check_requirements(void);
void xmhfhic_arch_setup_slab_device_allocation(void);
void xmhfhic_arch_setup_hypervisor_slab_page_tables(void);
void xmhfhic_arch_setup_guest_slab_page_tables(void);
void xmhfhic_arch_switch_to_smp(void);
void xmhfhic_arch_setup_base_cpu_data_structures(void);
void xmhf_hic_arch_setup_cpu_state(u64 cpuid);
void xmhfhic_smp_entry(u64 cpuid);
void xmhfhic_arch_relinquish_control_to_init_slab(u64 cpuid);



__attribute__((naked)) void __xmhfhic_rtm_trampoline_stub(void);
void __xmhfhic_rtm_trampoline(u64 cpuid, slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 dst_slabid);







typedef struct {
	u64 start;
	u64 end;
} slab_section_t;

typedef void * slab_entrystub_t;

typedef struct {
	u64 slab_index;
	u64 slab_macmid;
	u64 slab_privilegemask;
	u64 slab_tos;
	slab_section_t slab_code;
	slab_section_t slab_rodata;
	slab_section_t slab_rwdata;
	slab_section_t slab_stack;
	slab_entrystub_t entrystub;
} slab_header_t;


typedef struct {
	bool desc_valid;
	u64 numdevices;
    xc_platformdevice_arch_desc_t arch_desc[MAX_PLATFORM_DEVICES];
} __attribute__((packed)) xc_platformdevice_desc_t;

//slab interface aggregate return type
typedef union {
		bool retval_bool;
		u8 retval_u8;
		u16 retval_u16;
		u32 retval_u32;
		u64 retval_u64;
		struct regs retval_regs;
		context_desc_t retval_context_desc;
		xc_hypapp_arch_param_t retval_xc_hypapp_arch_param;
        xc_platformdevice_desc_t retval_xc_platformdevice_desc;
}__attribute__((packed)) slab_retval_t;

typedef struct {
    bool input_bool[8];
    u64 input_u64[8];
    u32 input_u32[8];
    u16 input_u16[8];
    u8 input_u8[8];
    struct regs input_regs;
    context_desc_t input_context_desc;
    xc_hypapp_arch_param_t input_xc_hypapp_arch_param;
    xc_platformdevice_desc_t input_xc_platformdevice_desc;
}__attribute__((packed)) slab_params_t;


extern __attribute__(( section(".sharedro_xcbootinfoptr") )) XMHF_BOOTINFO *xcbootinfo;
extern slab_header_t _slab_table[XMHF_SLAB_NUMBEROFSLABS];















//////
//arch. dependent decls.

extern __attribute__(( aligned(16) )) u64 __xmhfhic_x86vmx_gdt_start[];
extern __attribute__(( aligned(16) )) arch_x86_gdtdesc_t __xmhfhic_x86vmx_gdt;
extern __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss[MAX_PLATFORM_CPUS][PAGE_SIZE_4K];
extern __attribute__(( aligned(8) )) u64 __xmhfhic_x86vmx_cpuidtable[MAX_X86_APIC_ID];
extern u64  __xmhfhic_exceptionstubs[];
extern __attribute__(( aligned(16) )) idtentry_t __xmhfhic_x86vmx_idt_start[EMHF_XCPHANDLER_MAXEXCEPTIONS];
extern __attribute__(( aligned(16) )) arch_x86_idtdesc_t __xmhfhic_x86vmx_idt;
extern __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss_stack[MAX_PLATFORM_CPUS][PAGE_SIZE_4K];
extern __attribute__(( aligned(4096) )) xc_cpuarchdata_x86vmx_t __xmhfhic_x86vmx_archdata[MAX_PLATFORM_CPUS];
extern __attribute__(( aligned(4096) )) u8 __xmhfhic_rtm_trampoline_stack[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];




//////
//



//#define XMHF_SLAB_CALL(dst_slabname, dst_slabid, cpuid, iparams, iparams_size, oparams, oparams_size) dst_slabname##_interface(cpuid, iparams, iparams_size, oparams, oparams_size)
#define XMHF_SLAB_CALL(dst_slabname, dst_slabid, cpuid, iparams, iparams_size, oparams, oparams_size) __slab_callstub(cpuid, iparams, iparams_size, oparams, oparams_size, dst_slabid)


#define XMHF_SLAB(slab_name)	\
	__attribute__ ((section(".stack"))) u8 slab_name##_slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".data"))) u64 slab_name##_slab_tos[MAX_PLATFORM_CPUS]= { ((u64)&slab_name##_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
																				\
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub_##slab_name(void){	\
	asm volatile (							\
            "movq "#slab_name"_slab_tos+0x0(,%%edi,8), %%rsp \r\n" \
            "cmpq $0, %%r8 \r\n" \
            "je 1f \r\n" \
            "subq %%r8, %%rsp \r\n" \
            "movq %%rsp, %%rcx \r\n" \
            "1: \r\n" \
                            \
            "callq "#slab_name"_interface \r\n"		\
                        \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:								\
			: 	\
               \
			:								\
		);									\
    }\
    \
    \
    \
    __attribute__((naked)) __attribute__ ((noinline)) static inline bool __slab_callstub(u64 cpuid, slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 dst_slabid){\
        asm volatile ( \
            "movq %%rsp, "#slab_name"_slab_tos+0x0(,%%edi,8) \r\n"  \
            \
            \
            "jmp _slab_trampolinenew \r\n" \
            \
            \
            "1:\r\n" \
            "movq "#slab_name"_slab_tos+0x0(,%%edi,8), %%rsp \r\n" \
                    \
                    \
            \
            \
            "retq \r\n" \
            : \
            : \
            : \
        ); \
    } \

/*
    _slab_callstub: entry registers
    RDI = cpuid
    RSI = iparams
    RDX = iparams_size
    RCX = oparams
    R8 = oparmams_size
    R9 = dst_slabid

    R10 = available
    R11 = available
    RAX = available
*/



#endif //__ASSEMBLY__

#endif //__XMHF_HIC_H__
