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

#if defined (__XMHF_VERIFICATION__)

#define XMHF_HIC_MAX_SLABS                  (2)

#else

#define XMHF_HIC_MAX_SLABS                  (9)


#endif //__XMHF_VERIFICATION__


#define XMHF_HYP_SLAB_XCINIT                (0)
#define XMHF_HYP_SLAB_XCIHUB                (1)
#define XMHF_HYP_SLAB_XCEXHUB               (2)
#define XMHF_HYP_SLAB_XCTESTSLAB1           (3)
#define XMHF_HYP_SLAB_XHHYPERDEP            (4)
#define XMHF_HYP_SLAB_XHAPPROVEXEC          (5)
#define XMHF_HYP_SLAB_XHSYSCALLLOG          (6)
#define XMHF_HYP_SLAB_XHSSTEPTRACE          (7)
#define XMHF_GUEST_SLAB_XCGUESTSLAB         (8)


#define XMHF_HIC_SLABCALL                   (0xA0)
#define XMHF_HIC_SLABRET                    (0xA1)

#define XMHF_HIC_SLABCALLEXCEPTION          (0xA2)
#define XMHF_HIC_SLABRETEXCEPTION           (0xA3)

#define XMHF_HIC_SLABCALLINTERCEPT          (0xA4)
#define XMHF_HIC_SLABRETINTERCEPT           (0xA5)


#define XMHF_HIC_UAPI                       (0x666)

#define XMHF_HIC_UAPI_CPUSTATE                  (0)

#define XMHF_HIC_UAPI_CPUSTATE_VMREAD           (1)
#define XMHF_HIC_UAPI_CPUSTATE_VMWRITE          (2)
#define XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD    (3)
#define XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE   (4)
#define XMHF_HIC_UAPI_CPUSTATE_WRMSR            (5)
#define XMHF_HIC_UAPI_CPUSTATE_RDMSR            (6)


#define XMHF_HIC_UAPI_PHYSMEM                   (16)

#define XMHF_HIC_UAPI_PHYSMEM_PEEK              (17)
#define XMHF_HIC_UAPI_PHYSMEM_POKE              (18)

#define XMHF_HIC_UAPI_MEMPGTBL                  (24)

#define XMHF_HIC_UAPI_MEMPGTBL_GETENTRY         (25)
#define XMHF_HIC_UAPI_MEMPGTBL_SETENTRY         (26)



#ifndef __ASSEMBLY__


typedef void slab_input_params_t;
typedef void slab_output_params_t;
typedef void * slab_entrystub_t;

typedef u64 slab_privilegemask_t;
typedef u64 slab_callcaps_t;
typedef u64 slab_uapicaps_t;

typedef struct {
	bool desc_valid;
	u64 numdevices;
    xc_platformdevice_arch_desc_t arch_desc[MAX_PLATFORM_DEVICES];
} __attribute__((packed)) slab_platformdevices_t;


//slab capabilities type
typedef struct {
    slab_privilegemask_t slab_privilegemask;
    slab_callcaps_t slab_callcaps;
    slab_uapicaps_t slab_uapicaps;
    slab_platformdevices_t slab_devices;
    u64 slab_archparams;
} __attribute__((packed)) slab_caps_t;



#define HIC_SLAB_CALLCAP(x) (1 << x)
#define HIC_SLAB_UAPICAP(x) (1 << x)




//////
// uapi related types

typedef struct {
    u64 guest_slab_index;
    void *addr_from;
    void *addr_to;
    u64 numbytes;
}__attribute__((packed)) xmhf_hic_uapi_physmem_desc_t;

typedef struct {
    u64 guest_slab_index;
    u64 gpa;
    u64 entry;
}__attribute__((packed)) xmhf_hic_uapi_mempgtbl_desc_t;









typedef struct {
    u64 src_slabid;
    u64 dst_slabid;
    u64 hic_calltype;
    u64 return_address;
    slab_output_params_t *oparams;
    slab_output_params_t *newoparams;
    u64 oparams_size;
    u64 iparams_size;
} __xmhfhic_safestack_element_t;


#define HIC_SLAB_PHYSMEM_EXTENT_READ       (1 << 0)
#define HIC_SLAB_PHYSMEM_EXTENT_WRITE      (1 << 1)
#define HIC_SLAB_PHYSMEM_EXTENT_EXECUTE    (1 << 2)

#define HIC_SLAB_PHYSMEM_MAXEXTENTS         5

//slab physical memory extent type
typedef struct {
    u64 addr_start;
    u64 addr_end;
    u64 protection;
} slab_physmem_extent_t;


typedef struct {
    __attribute__((aligned(4096))) slab_info_archdata_t archdata;
	bool slab_inuse;
    slab_privilegemask_t slab_privilegemask;
    slab_callcaps_t slab_callcaps;
    slab_uapicaps_t slab_uapicaps;
    slab_platformdevices_t slab_devices;
    slab_physmem_extent_t slab_physmem_extents[HIC_SLAB_PHYSMEM_MAXEXTENTS];
	slab_entrystub_t entrystub;
} __attribute__((packed)) __attribute__((aligned(4096))) slab_info_t;







//////
//modified data types
typedef struct {
	u64 *mempgtbl_pdpt;
	u64 *mempgtbl_pdt;
	u64 *mempgtbl_pt;
	u64 *devpgtbl;
	u8  *deviomap;
	u64 slabtype; //hypervisor, guest
	bool mempgtbl_initialized;
	bool devpgtbl_initialized;
	u64 mempgtbl_cr3;
	u64 slabtos[MAX_PLATFORM_CPUS];
} __attribute__((packed)) __attribute__((aligned(4096))) x_slab_info_archdata_t;


typedef struct {
    __attribute__((aligned(4096))) x_slab_info_archdata_t archdata;
	bool slab_inuse;
    slab_privilegemask_t slab_privilegemask;
    slab_callcaps_t slab_callcaps;
    slab_uapicaps_t slab_uapicaps;
    slab_platformdevices_t slab_devices;
    slab_physmem_extent_t slab_physmem_extents[HIC_SLAB_PHYSMEM_MAXEXTENTS];
	slab_entrystub_t entrystub;
} __attribute__((packed)) __attribute__((aligned(4096))) x_slab_info_t;






#define GUEST_SLAB_HEADER_MAGIC     (0x76543210)
//guest slab header data type
typedef struct {
    u64 magic;
    __attribute__((aligned(4096))) u64 lvl2mempgtbl_pml4t[PAE_MAXPTRS_PER_PDPT];
    __attribute__((aligned(4096))) u64 lvl2mempgtbl_pdpt[PAE_MAXPTRS_PER_PDPT];
    __attribute__((aligned(4096))) u64 lvl2mempgtbl_pdts[PAE_PTRS_PER_PDPT][PAE_PTRS_PER_PDT];
    __attribute__(( aligned(16) )) u64 gdt[16];
} __attribute__((packed)) guest_slab_header_t;





//////
// HIC function prototypes

void xmhfhic_arch_setup_slab_info(void);
void xmhfhic_arch_sanity_check_requirements(void);
void xmhfhic_arch_setup_slab_device_allocation(void);
void xmhfhic_arch_setup_slab_mem_page_tables(void);
void xmhfhic_arch_switch_to_smp(void);
void xmhfhic_arch_setup_base_cpu_data_structures(void);
void xmhf_hic_arch_setup_cpu_state(u64 cpuid);
void xmhfhic_smp_entry(u64 cpuid);
void xmhfhic_arch_relinquish_control_to_init_slab(u64 cpuid);



bool __xmhfhic_callcaps(u64 src_slabid, u64 dst_slabid);

void __xmhfhic_safepush(u64 cpuid, u64 src_slabid, u64 dst_slabid, u64 hic_calltype, u64 return_address,
                        slab_output_params_t *oparams, slab_output_params_t *newoparams, u64 oparams_size, u64 iparams_size);

void __xmhfhic_safepop(u64 cpuid, u64 *src_slabid, u64 *dst_slabid, u64 *hic_calltype, u64 *return_address,
                       slab_output_params_t **oparams, slab_output_params_t **newoparams, u64 *oparams_size, u64 *iparams_size);


__attribute__((naked)) void __xmhfhic_rtm_intercept_stub(void);
__attribute__((naked)) void __xmhfhic_rtm_trampoline_stub(void);
void __xmhfhic_rtm_trampoline(u64 hic_calltype, slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 dst_slabid, u64 src_slabid, u64 cpuid, u64 return_address, u64 return_rsp);
void __xmhfhic_rtm_uapihandler(u64 uapicall, u64 uapicall_num, u64 uapicall_subnum,
                               u64 reserved, u64 iparams, u64 oparams,
                               u64 src_slabid, u64 cpuid);



//////
// HIC data decls.


//init, setup data
extern __attribute__(( section(".sharedro_xcbootinfoptr") )) XMHF_BOOTINFO *xcbootinfo; //ro
extern slab_physmem_extent_t _xmhfhic_init_setupdata_slab_physmem_extents[XMHF_HIC_MAX_SLABS][HIC_SLAB_PHYSMEM_MAXEXTENTS]; //ro
extern slab_physmem_extent_t _xmhfhic_init_setupdata_hic_physmem_extents[HIC_SLAB_PHYSMEM_MAXEXTENTS]; //ro
extern slab_caps_t _xmhfhic_init_setupdata_slab_caps[XMHF_HIC_MAX_SLABS]; //ro


//runtime data
extern __attribute__((aligned(4096))) slab_info_t _xmhfhic_common_slab_info_table[XMHF_HIC_MAX_SLABS];
extern slab_physmem_extent_t _xmhfhic_common_hic_physmem_extents[HIC_SLAB_PHYSMEM_MAXEXTENTS]; //ro
extern u64 __xmhfhic_safestack_indices[MAX_PLATFORM_CPUS];
extern __xmhfhic_safestack_element_t __xmhfhic_safestack[MAX_PLATFORM_CPUS][512];

//arch. dependent runtime data
extern __attribute__(( aligned(16) )) u64 __xmhfhic_x86vmx_gdt_start[];     //ro
extern __attribute__(( aligned(16) )) arch_x86_gdtdesc_t __xmhfhic_x86vmx_gdt;  //ro
extern __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss[MAX_PLATFORM_CPUS][PAGE_SIZE_4K]; //ro
extern __attribute__(( aligned(8) )) u64 __xmhfhic_x86vmx_cpuidtable[MAX_X86_APIC_ID]; //ro
extern u64  __xmhfhic_exceptionstubs[]; //ro
extern __attribute__(( aligned(16) )) idtentry_t __xmhfhic_x86vmx_idt_start[EMHF_XCPHANDLER_MAXEXCEPTIONS]; //ro
extern __attribute__(( aligned(16) )) arch_x86_idtdesc_t __xmhfhic_x86vmx_idt; //ro
extern __attribute__(( aligned(4096) )) u8 _init_cpustacks[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE]; //ro
extern __attribute__(( aligned(2097152) )) u64 _xmhfhic_common_slab_archdata_mempgtbl_pml4t[XMHF_HIC_MAX_SLABS][PAE_MAXPTRS_PER_PML4T]; //ro


extern __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss_stack[MAX_PLATFORM_CPUS][PAGE_SIZE_4K];
extern __attribute__(( aligned(4096) )) u8 __xmhfhic_rtm_trampoline_stack[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];
extern __attribute__(( aligned(4096) )) xc_cpuarchdata_x86vmx_t __xmhfhic_x86vmx_archdata[MAX_PLATFORM_CPUS];

//libxmhfdebug
extern __attribute__(( section(".libxmhfdebugdata") )) u32 libxmhfdebug_lock;












//////
// HIC UAPI and SLAB invocation macros



//HIC UAPI


/*
__xmhfhic_uapi_cpustate register mappings:

RDI = XMHF_HIC_UAPI
RSI = XMHF_HIC_UAPI_CPUSTATE
RDX = cpustatefn
RCX = undefined
R8 = iparams
R9 = oparams
R10 = return RSP
R11 = return_address

*/

//reserved_uapicall = XMHF_HIC_UAPI, reserved_uapicall_num = XMHF_HIC_UAPI_CPUSTATE
__attribute__((naked)) __attribute__ ((noinline)) static inline bool __xmhfhic_uapi_cpustate(u64 reserved_uapicall, u64 reserved_uapicall_num,
                                           u64 cpustatefn,
                                           u64 reserved, u64 iparams, u64 oparams){

    asm volatile (
        "movq %%rsp, %%r10 \r\n"
        "movq $1f, %%r11 \r\n"\
        "sysenter \r\n" \
        \
        "1:\r\n" \
        "retq \r\n" \
        :
        :
        :
    );


}


#if defined (__XMHF_VERIFICATION)

#define XMHF_HIC_SLAB_UAPI_CPUSTATE(cpustatefn, iparams, oparams)

#else

#define XMHF_HIC_SLAB_UAPI_CPUSTATE(cpustatefn, iparams, oparams) \
    __xmhfhic_uapi_cpustate(XMHF_HIC_UAPI, XMHF_HIC_UAPI_CPUSTATE, cpustatefn, 0, iparams, oparams)

#endif //__XMHF_VERIFICATION__







/*
__xmhfhic_uapi_physmem register mappings:

RDI = XMHF_HIC_UAPI
RSI = XMHF_HIC_UAPI_PHYSMEM
RDX = physmemfn
RCX = undefined
R8 = iparams
R9 = oparams
R10 = return RSP
R11 = return_address

*/

//reserved_uapicall = XMHF_HIC_UAPI, reserved_uapicall_num = XMHF_HIC_UAPI_PHYSMEM
__attribute__((naked)) __attribute__ ((noinline)) static inline bool __xmhfhic_uapi_physmem(u64 reserved_uapicall, u64 reserved_uapicall_num,
                                           u64 physmemfn,
                                           u64 reserved, u64 iparams, u64 oparams){

    asm volatile (
        "movq %%rsp, %%r10 \r\n"
        "movq $1f, %%r11 \r\n"\
        "sysenter \r\n" \
        \
        "1:\r\n" \
        "retq \r\n" \
        :
        :
        :
    );


}

#if defined (__XMHF_VERIFICATION__)

#define XMHF_HIC_SLAB_UAPI_PHYSMEM(physmemfn, iparams, oparams)


#else

#define XMHF_HIC_SLAB_UAPI_PHYSMEM(physmemfn, iparams, oparams) \
    __xmhfhic_uapi_physmem(XMHF_HIC_UAPI, XMHF_HIC_UAPI_PHYSMEM, physmemfn, 0, iparams, oparams)


#endif






/*
__xmhfhic_uapi_mempgtbl register mappings:

RDI = XMHF_HIC_UAPI
RSI = XMHF_HIC_UAPI_MEMPGTBL
RDX = mempgtblfn
RCX = undefined
R8 = iparams
R9 = oparams
R10 = return RSP
R11 = return_address

*/

//reserved_uapicall = XMHF_HIC_UAPI, reserved_uapicall_num = XMHF_HIC_UAPI_MEMPGTBL
__attribute__((naked)) __attribute__ ((noinline)) static inline bool __xmhfhic_uapi_mempgtbl(u64 reserved_uapicall, u64 reserved_uapicall_num,
                                           u64 mempgtblfn,
                                           u64 reserved, u64 iparams, u64 oparams){

    asm volatile (
        "movq %%rsp, %%r10 \r\n"
        "movq $1f, %%r11 \r\n"\
        "sysenter \r\n" \
        \
        "1:\r\n" \
        "retq \r\n" \
        :
        :
        :
    );


}


#if defined (__XMHF_VERIFICATION__)

#define XMHF_HIC_SLAB_UAPI_MEMPGTBL(mempgtblfn, iparams, oparams) \
    __xmhfhic_uapi_mempgtbl(XMHF_HIC_UAPI, XMHF_HIC_UAPI_MEMPGTBL, mempgtblfn, 0, iparams, oparams)


#else

#define XMHF_HIC_SLAB_UAPI_MEMPGTBL(mempgtblfn, iparams, oparams)

#endif //__XMHF_VERIFICATION__




/*
__slab_callstub register mappings:

RDI = call type (XMHF_HIC_SLABCALL)
RSI = iparams
RDX = iparams_size
RCX = oparams
R8 = oparams_size
R9 = dst_slabid
R10 = return RSP;
R11 = return_address

*/


__attribute__((naked)) __attribute__ ((noinline)) static inline bool __slab_callstub(u64 reserved, slab_input_params_t *iparams, u64 iparams_size, slab_output_params_t *oparams, u64 oparams_size, u64 dst_slabid){
    asm volatile (
        "pushq %%rbx \r\n"
        "pushq %%r12 \r\n"
        "pushq %%r13 \r\n"
        "pushq %%r14 \r\n"
        "pushq %%r15 \r\n"

        "movq %0, %%rdi \r\n"
        "movq %%rsp, %%r10 \r\n"
        "movq $1f, %%r11 \r\n"\
        "sysenter \r\n" \
        \
        "1:\r\n" \
        "popq %%r15 \r\n"
        "popq %%r14 \r\n"
        "popq %%r13 \r\n"
        "popq %%r12 \r\n"
        "popq %%rbx \r\n"
        "retq \r\n" \
        :
        : "i" (XMHF_HIC_SLABCALL)
        :
    );
}


#if defined (__XMHF_VERIFICATION__)

#define XMHF_SLAB_CALL(dst_slabname, dst_slabid, iparams, iparams_size, oparams, oparams_size)
#define XMHF_SLAB(slab_name)
#define XMHF_SLAB_GUEST(slab_name)
#define XMHF_SLAB_INTERCEPT(slab_name)
#define XMHF_SLAB_EXCEPTION(slab_name)


#else




#define XMHF_SLAB_CALL(dst_slabname, dst_slabid, iparams, iparams_size, oparams, oparams_size) __slab_callstub(0, iparams, iparams_size, oparams, oparams_size, dst_slabid)


/*
_slab_entrystub entry register mappings:

RDI = iparams
RSI = iparams_size
RDX = slab entrystub; used for SYSEXIT
RCX = slab entrystub stack TOS for the CPU; used for SYSEXIT
R8 = oparams
R9 = oparams_size
R10 = src_slabid
R11 = cpuid

*/


#define XMHF_SLAB(slab_name)	\
	__attribute__ ((section(".rodata"))) char * slab_name##_string="_xmhfslab_"#slab_name"_";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 slab_name##_slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u64 slab_name##_slab_tos[MAX_PLATFORM_CPUS]= { ((u64)&slab_name##_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 slab_name##dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub_##slab_name(void){	\
	asm volatile ( \
            "pushq %%r10 \r\n" \
            "movq %%r8, %%rdx \r\n" \
            "movq %%r9, %%rcx \r\n" \
            "movq %%r10, %%r8 \r\n" \
            "movq %%r11, %%r9 \r\n" \
            "callq "#slab_name"_interface \r\n"		\
            "popq %%r9 \r\n" \
            "movq %0, %%rdi \r\n" \
            "sysenter \r\n" \
            \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRET) \
			:  \
		);	\
    }\



#define XMHF_SLAB_GUEST(slab_name)	\
	__attribute__ ((section(".rodata"))) char * slab_name##_string="_xmhfslab_"#slab_name"_";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 slab_name##_slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u64 slab_name##_slab_tos[MAX_PLATFORM_CPUS]= { ((u64)&slab_name##_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 slab_name##dmadataplaceholder[1];\
    __attribute__ ((section(".rwdatahdr"))) guest_slab_header_t slab_name##_guestslabheader = {GUEST_SLAB_HEADER_MAGIC, 0};\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub_##slab_name(void){	\
	asm volatile ( \
          "jmp "#slab_name"_interface \r\n"		\
			:  \
			:  \
			:  \
		);	\
    }\



#define XMHF_SLAB_INTERCEPT(slab_name)	\
	__attribute__ ((section(".rodata"))) char * slab_name##_string="_xmhfslab_"#slab_name"_";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 slab_name##_slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u64 slab_name##_slab_tos[MAX_PLATFORM_CPUS]= { ((u64)&slab_name##_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 slab_name##dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub_##slab_name(void){	\
	asm volatile ( \
            "pushq %%r10 \r\n" \
            "movq %%r8, %%rdx \r\n" \
            "movq %%r9, %%rcx \r\n" \
            "movq %%r10, %%r8 \r\n" \
            "movq %%r11, %%r9 \r\n" \
            "callq "#slab_name"_interface \r\n"		\
            "popq %%r9 \r\n" \
            "movq %0, %%rdi \r\n" \
            "sysenter \r\n" \
            \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRETINTERCEPT) \
			:  \
		);	\
    }\



#define XMHF_SLAB_EXCEPTION(slab_name)	\
	__attribute__ ((section(".rodata"))) char * slab_name##_string="_xmhfslab_"#slab_name"_";	\
	__attribute__ ((section(".stack"))) __attribute__ ((aligned(4096))) u8 slab_name##_slab_stack[MAX_PLATFORM_CPUS][XMHF_SLAB_STACKSIZE];	\
	__attribute__ ((section(".stackhdr"))) u64 slab_name##_slab_tos[MAX_PLATFORM_CPUS]= { ((u64)&slab_name##_slab_stack[0] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[1] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[2] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[3] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[4] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[5] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[6] + XMHF_SLAB_STACKSIZE), ((u64)&slab_name##_slab_stack[7] + XMHF_SLAB_STACKSIZE)  };	\
    __attribute__ ((section(".slab_dmadata"))) u8 slab_name##dmadataplaceholder[1];\
    \
    \
	__attribute__((naked)) __attribute__ ((section(".slab_entrystub"))) __attribute__((align(1))) void _slab_entrystub_##slab_name(void){	\
	asm volatile ( \
            "pushq %%r10 \r\n" \
            "movq %%r8, %%rdx \r\n" \
            "movq %%r9, %%rcx \r\n" \
            "movq %%r10, %%r8 \r\n" \
            "movq %%r11, %%r9 \r\n" \
            "callq "#slab_name"_interface \r\n"		\
            "popq %%r9 \r\n" \
            "movq %0, %%rdi \r\n" \
            "sysenter \r\n" \
            \
            "int $0x03 \r\n" \
            "1: jmp 1b \r\n" \
            \
			:  \
			:  "i" (XMHF_HIC_SLABRETEXCEPTION) \
			:  \
		);	\
    }\




#endif //__XMHF_VERIFICATION__



#endif //__ASSEMBLY__

#endif //__XMHF_HIC_H__


