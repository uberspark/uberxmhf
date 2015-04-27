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

/*
 * guest CPU state uAPI
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <geec_primesmp.h>
#include <geec_sentinel.h>
#include <xc_init.h>

//////
// data
//////

extern void __xmhf_exception_handler_0(void);
extern void __xmhf_exception_handler_1(void);
extern void __xmhf_exception_handler_2(void);
extern void __xmhf_exception_handler_3(void);
extern void __xmhf_exception_handler_4(void);
extern void __xmhf_exception_handler_5(void);
extern void __xmhf_exception_handler_6(void);
extern void __xmhf_exception_handler_7(void);
extern void __xmhf_exception_handler_8(void);
extern void __xmhf_exception_handler_9(void);
extern void __xmhf_exception_handler_10(void);
extern void __xmhf_exception_handler_11(void);
extern void __xmhf_exception_handler_12(void);
extern void __xmhf_exception_handler_13(void);
extern void __xmhf_exception_handler_14(void);
extern void __xmhf_exception_handler_15(void);
extern void __xmhf_exception_handler_16(void);
extern void __xmhf_exception_handler_17(void);
extern void __xmhf_exception_handler_18(void);
extern void __xmhf_exception_handler_19(void);
extern void __xmhf_exception_handler_20(void);
extern void __xmhf_exception_handler_21(void);
extern void __xmhf_exception_handler_22(void);
extern void __xmhf_exception_handler_23(void);
extern void __xmhf_exception_handler_24(void);
extern void __xmhf_exception_handler_25(void);
extern void __xmhf_exception_handler_26(void);
extern void __xmhf_exception_handler_27(void);
extern void __xmhf_exception_handler_28(void);
extern void __xmhf_exception_handler_29(void);
extern void __xmhf_exception_handler_30(void);
extern void __xmhf_exception_handler_31(void);

#define XMHF_EXCEPTION_HANDLER_ADDROF(vector) &__xmhf_exception_handler_##vector

u32  __xmhfhic_exceptionstubs[] = { XMHF_EXCEPTION_HANDLER_ADDROF(0),
							XMHF_EXCEPTION_HANDLER_ADDROF(1),
							XMHF_EXCEPTION_HANDLER_ADDROF(2),
							XMHF_EXCEPTION_HANDLER_ADDROF(3),
							XMHF_EXCEPTION_HANDLER_ADDROF(4),
							XMHF_EXCEPTION_HANDLER_ADDROF(5),
							XMHF_EXCEPTION_HANDLER_ADDROF(6),
							XMHF_EXCEPTION_HANDLER_ADDROF(7),
							XMHF_EXCEPTION_HANDLER_ADDROF(8),
							XMHF_EXCEPTION_HANDLER_ADDROF(9),
							XMHF_EXCEPTION_HANDLER_ADDROF(10),
							XMHF_EXCEPTION_HANDLER_ADDROF(11),
							XMHF_EXCEPTION_HANDLER_ADDROF(12),
							XMHF_EXCEPTION_HANDLER_ADDROF(13),
							XMHF_EXCEPTION_HANDLER_ADDROF(14),
							XMHF_EXCEPTION_HANDLER_ADDROF(15),
							XMHF_EXCEPTION_HANDLER_ADDROF(16),
							XMHF_EXCEPTION_HANDLER_ADDROF(17),
							XMHF_EXCEPTION_HANDLER_ADDROF(18),
							XMHF_EXCEPTION_HANDLER_ADDROF(19),
							XMHF_EXCEPTION_HANDLER_ADDROF(20),
							XMHF_EXCEPTION_HANDLER_ADDROF(21),
							XMHF_EXCEPTION_HANDLER_ADDROF(22),
							XMHF_EXCEPTION_HANDLER_ADDROF(23),
							XMHF_EXCEPTION_HANDLER_ADDROF(24),
							XMHF_EXCEPTION_HANDLER_ADDROF(25),
							XMHF_EXCEPTION_HANDLER_ADDROF(26),
							XMHF_EXCEPTION_HANDLER_ADDROF(27),
							XMHF_EXCEPTION_HANDLER_ADDROF(28),
							XMHF_EXCEPTION_HANDLER_ADDROF(29),
							XMHF_EXCEPTION_HANDLER_ADDROF(30),
							XMHF_EXCEPTION_HANDLER_ADDROF(31),
};

// CASM module supporting data structures

// initialization phase CPU stacks
__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) u8 _init_cpustacks[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];


// following two data structures used for SMP bootup
__attribute__(( aligned(16) )) u64 _xcsmp_ap_init_gdt_start[]  = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00af9b000000ffffULL,	//CPL-0 64-bit code descriptor (CS64)
	0x00af93000000ffffULL,	//CPL-0 64-bit data descriptor (DS/SS/ES/FS/GS)
};

__attribute__(( aligned(16) )) arch_x86_gdtdesc_t _xcsmp_ap_init_gdt  = {
	.size=sizeof(_xcsmp_ap_init_gdt_start)-1,
	.base=&_xcsmp_ap_init_gdt_start,
};



//static bool CASM_FUNCCALL(__xmhfhic_ap_entry,void) __attribute__((naked));
void __xmhfhic_smp_cpu_x86_smpinitialize_commonstart(void);
static u64 _xcsmp_ap_entry_lock = 1;
static mtrr_state_t _mtrrs;
u64 _ap_cr3=0;


// GDT
__attribute__((section(".data"))) __attribute__(( aligned(16) )) u64 __xmhfhic_x86vmx_gdt_start[]  = {
	0x0000000000000000ULL,	//NULL descriptor
	0x00cf9a000000ffffULL,	//CPL-0 32-bit code descriptor (CS64)
	0x00cf92000000ffffULL,	//CPL-0 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x00cffa000000ffffULL,	//TODO: CPL-3 32-bit code descriptor (CS64)
	0x00cff2000000ffffULL,	//TODO: CPL-3 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x00cffa000000ffffULL,	//TODO: CPL-3 32-bit code descriptor (CS64)
	0x00cff2000000ffffULL,	//TODO: CPL-3 32-bit data descriptor (DS/SS/ES/FS/GS)
	0x0000000000000000ULL,  //TSS descriptors (64-bits each)
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,
	0x0000000000000000ULL,

	0x0000000000000000ULL,
};
// GDT descriptor
__attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_gdtdesc_t __xmhfhic_x86vmx_gdt  = {
	.size=sizeof(__xmhfhic_x86vmx_gdt_start)-1,
	.base=(u32)&__xmhfhic_x86vmx_gdt_start,
};


// TSS
__attribute__((section(".data"))) __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss[MAX_PLATFORM_CPUS][PAGE_SIZE_4K] = { 0 };
// TSS stacks
__attribute__((section(".data"))) __attribute__(( aligned(4096) )) u8 __xmhfhic_x86vmx_tss_stack[MAX_PLATFORM_CPUS][PAGE_SIZE_4K];


// IDT
__attribute__((section(".data"))) __attribute__(( aligned(16) )) idtentry_t __xmhfhic_x86vmx_idt_start[EMHF_XCPHANDLER_MAXEXCEPTIONS] ;
// IDT descriptor
__attribute__((section(".data"))) __attribute__(( aligned(16) )) arch_x86_idtdesc_t __xmhfhic_x86vmx_idt = {
	.size=sizeof(__xmhfhic_x86vmx_idt_start)-1,
	.base=(u32)&__xmhfhic_x86vmx_idt_start,
};


// sysenter CPU stacks
__attribute__(( section(".stack") )) __attribute__(( aligned(4096) )) u8 _geec_primesmp_sysenter_stack[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE];


__attribute__((section(".data"))) __attribute__(( aligned(4) )) u32 __xmhfhic_x86vmx_cpuidtable[MAX_X86_APIC_ID];

__attribute__((section(".data"))) __attribute__(( aligned(4096) )) xc_cpuarchdata_x86vmx_t __xmhfhic_x86vmx_archdata[MAX_PLATFORM_CPUS];



//////
// code
//////


//set IOPl to CPl-3
static void __xmhfhic_x86vmx_setIOPL3(u64 cpuid){
    u32 eflags;
    eflags = CASM_FUNCCALL(read_eflags,CASM_NOPARAM);
    eflags |= EFLAGS_IOPL;
 CASM_FUNCCALL(write_eflags,eflags);
}


//////////////////////////////////////////////////////////////////////////////
// switch to smp





static void __xmhfhic_smp_cpu_x86_savecpumtrrstate(void){
	xmhfhw_cpu_x86_save_mtrrs(&_mtrrs);
}

static void __xmhfhic_smp_cpu_x86_restorecpumtrrstate(void){
	xmhfhw_cpu_x86_restore_mtrrs(&_mtrrs);
}


//wake up APs using the LAPIC by sending the INIT-SIPI-SIPI IPI sequence
static void __xmhfhic_smp_cpu_x86_wakeupAPs(void){
	u32 eax, edx;
	volatile u32 *icr;

	//read LAPIC base address from MSR
	rdmsr(MSR_APIC_BASE, &eax, &edx);
	HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G

	//construct the command register address (offset 0x300)
	icr = (u32 *) (((u32)eax & 0xFFFFF000UL) + 0x300);

	//our AP boot-strap code is at physical memory location 0x10000.
	//so use 0x10 as the vector (0x10000/0x1000 = 0x10)

	//send INIT
	*icr = 0x000c4500UL;

	xmhf_baseplatform_arch_x86_udelay(10000);

	//wait for command completion
	{
		u32 val;
		do{
		  val = *icr;
		}while( (val & 0x1000) );
	}

	//send SIPI (twice as per the MP protocol)
	{
		int i;
		for(i=0; i < 2; i++){
			*icr = 0x000c4610UL;
			xmhf_baseplatform_arch_x86_udelay(200);
			//wait for command completion
			{
			  u32 val;
			  do{
				val = *icr;
			  }while( (val & 0x1000) );
			}
		}
	}

}



//wake up application processors (cores) in the system
static void __xmhfhic_smp_container_vmx_wakeupAPs(void){
    static x86smp_apbootstrapdata_t apdata;

    apdata.ap_cr3 = CASM_FUNCCALL(read_cr3,CASM_NOPARAM);
    apdata.ap_cr4 = CASM_FUNCCALL(read_cr4,CASM_NOPARAM);
    apdata.ap_entrypoint = (u32)&__xmhfhic_ap_entry;
    apdata.ap_gdtdesc_limit = sizeof(apdata.ap_gdt) - 1;
    //apdata.ap_gdtdesc_base = (X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_gdt);
    apdata.ap_gdtdesc_base = (X86SMP_APBOOTSTRAP_DATASEG << 4) + 48;
    apdata.ap_cs_selector = __CS_CPL0;
    apdata.ap_eip = (X86SMP_APBOOTSTRAP_CODESEG << 4);
    apdata.cpuidtable = (u32)&__xmhfhic_x86vmx_cpuidtable;
    apdata.ap_gdt[0] = 0x0000000000000000ULL;
    apdata.ap_gdt[1] = 0x00cf9a000000ffffULL;
    apdata.ap_gdt[2] = 0x00cf92000000ffffULL;

    _XDPRINTF_("%s: sizeof(apdata)=%u bytes\n", __func__, sizeof(apdata));
    _XDPRINTF_("  apdata.ap_gdtdesc_limit at %08x\n", &apdata.ap_gdtdesc_limit);
    _XDPRINTF_("  apdata.ap_gdt at %08x\n", &apdata.ap_gdt);

    memcpy((void *)(X86SMP_APBOOTSTRAP_DATASEG << 4), (void *)&apdata, sizeof(apdata));

    memcpy((void *)(X86SMP_APBOOTSTRAP_CODESEG << 4), (void *)&_ap_bootstrap_code, PAGE_SIZE_4K);

#if defined (__DRT__)
    {
        txt_heap_t *txt_heap;
        os_mle_data_t *os_mle_data;
        mle_join_t *mle_join;
        sinit_mle_data_t *sinit_mle_data;
        os_sinit_data_t *os_sinit_data;

        txt_heap = get_txt_heap();
        os_mle_data = get_os_mle_data_start(txt_heap);
        sinit_mle_data = get_sinit_mle_data_start(txt_heap);
        os_sinit_data = get_os_sinit_data_start(txt_heap);

        // enable SMIs on BSP before waking APs (which will enable them on APs)
        // because some SMM may take immediate SMI and hang if AP gets in first
        //_XDPRINTF_("Enabling SMIs on BSP\n");
        //__getsec_smctrl();

        //mle_join = (mle_join_t *)((u32)(X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_gdtdesc_limit));
        mle_join = (mle_join_t *)((u32)(X86SMP_APBOOTSTRAP_DATASEG << 4) + 16);

        _XDPRINTF_("\nBSP: mle_join.gdt_limit = %x", mle_join->gdt_limit);
        _XDPRINTF_("\nBSP: mle_join.gdt_base = %x", mle_join->gdt_base);
        _XDPRINTF_("\nBSP: mle_join.seg_sel = %x", mle_join->seg_sel);
        _XDPRINTF_("\nBSP: mle_join.entry_point = %x", mle_join->entry_point);

        write_priv_config_reg(TXTCR_MLE_JOIN, (uint64_t)(unsigned long)mle_join);

        if (os_sinit_data->capabilities & TXT_CAPS_T_RLP_WAKE_MONITOR) {
            _XDPRINTF_("\nBSP: joining RLPs to MLE with MONITOR wakeup");
            _XDPRINTF_("\nBSP: rlp_wakeup_addr = 0x%x", sinit_mle_data->rlp_wakeup_addr);
            *((uint32_t *)(unsigned long)(sinit_mle_data->rlp_wakeup_addr)) = 0x01;
        }else {
            _XDPRINTF_("\nBSP: joining RLPs to MLE with GETSEC[WAKEUP]");
            __getsec_wakeup();
            _XDPRINTF_("\nBSP: GETSEC[WAKEUP] completed");
        }
    }

#else //!__DRT__

    _XDPRINTF_("\nBSP: Using APIC to awaken APs...");
    __xmhfhic_smp_cpu_x86_wakeupAPs();
    _XDPRINTF_("\nBSP: APs should be awake.");

#endif


}

//initialize SMP
static bool __xmhfhic_smp_arch_smpinitialize(void){
	u32 i;

    //save cpu MTRR state which we will later replicate on all APs
	#if !defined(__XMHF_VERIFICATION__)
	__xmhfhic_smp_cpu_x86_savecpumtrrstate();
    #endif

    //save page table base which we will later replicate on all APs
    _ap_cr3 = CASM_FUNCCALL(read_cr3,CASM_NOPARAM);

	//wake up APS
	if(xcbootinfo->cpuinfo_numentries > 1){
	  __xmhfhic_smp_container_vmx_wakeupAPs();
	}

	//fall through to common code
	_XDPRINTF_("%s: Relinquishing BSP thread and moving to common...\n", __func__);
	__xmhfhic_smp_cpu_x86_smpinitialize_commonstart();

	_XDPRINTF_("%s:%u: Must never get here. Halting\n", __func__, __LINE__);
	HALT();

}

//return 1 if the calling CPU is the BSP
static bool __xmhfhic_smp_cpu_x86_isbsp(void){
  u32 eax, edx;
  //read LAPIC base address from MSR
  rdmsr(MSR_APIC_BASE, &eax, &edx);
  HALT_ON_ERRORCOND( edx == 0 ); //APIC is below 4G

  if(eax & 0x100)
    return true;
  else
    return false;
}


//common function which is entered by all CPUs upon SMP initialization
//note: this is specific to the x86 architecture backend
void __xmhfhic_smp_cpu_x86_smpinitialize_commonstart(void){
	u32 cpuid;
	#if !defined(__XMHF_VERIFICATION__)
	cpuid  = __xmhfhic_x86vmx_cpuidtable[xmhf_baseplatform_arch_x86_getcpulapicid()];
    #endif

    xmhfhic_smp_entry(cpuid);
}


void xmhfhic_arch_switch_to_smp(void){
	//initialize cpu table and total platform CPUs
	{
	    u32 i, j;
	    for(i=0; i < MAX_X86_APIC_ID; i++)
           // __xmhfhic_x86vmx_cpuidtable[i] = 0xFFFFFFFFFFFFFFFFULL;
            __xmhfhic_x86vmx_cpuidtable[i] = 0xFFFFFFFFUL;

	    for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
            u64 value = i;

            if(xcbootinfo->cpuinfo_buffer[i].isbsp)
                //value |= 0x8000000000000000ULL;
                value |= 0x80000000UL;

            //XXX: TODO sanity check xcbootinfo->cpuinfo_buffer[i].lapic_id < MAX_X86_APIC_ID
            __xmhfhic_x86vmx_cpuidtable[xcbootinfo->cpuinfo_buffer[i].lapic_id] = value;
        }
	}

    __xmhfhic_smp_arch_smpinitialize();

}


void xmhfhic_smp_entry(u32 cpuid){
    bool isbsp = (cpuid & 0x80000000UL) ? true : false;
    #if defined (__XMHF_VERIFICATION__)
    cpuid = 0;
    isbsp = true;
    #endif // defined


    //[debug] halt all APs
    //if(!isbsp){
    //    _XDPRINTF_("%s[%u,%u]: esp=%08x. AP Halting!\n",
    //        __func__, (u16)cpuid, isbsp, CASM_FUNCCALL(read_esp,));
    //    HALT();
    //}

    _XDPRINTF_("%s[%u,%u]: esp=%08x. Starting...\n",
            __func__, cpuid, isbsp, CASM_FUNCCALL(read_esp,CASM_NOPARAM));

    xmhf_hic_arch_setup_cpu_state((u16)cpuid);

    //_XDPRINTF_("%s[%u,%u]: Halting!\n", __func__, (u16)cpuid, isbsp);
    //HALT();


    //relinquish HIC initialization and move on to the first slab
    _XDPRINTF_("%s[%u]: proceeding to call init slab at %x\n", __func__, (u16)cpuid,
                _xmhfhic_common_slab_info_table[XMHFGEEC_SLAB_XC_INIT].entrystub);

    //xmhfhic_arch_relinquish_control_to_init_slab(cpuid,
    //    _xmhfhic_common_slab_info_table[XMHFGEEC_SLAB_XC_INIT].entrystub,
    //    _xmhfhic_common_slab_info_table[XMHFGEEC_SLAB_XC_INIT].archdata.mempgtbl_cr3,
    //    _xmhfhic_common_slab_info_table[XMHFGEEC_SLAB_XC_INIT].archdata.slabtos[(u32)cpuid]);

    {
        slab_params_t sp;

        memset(&sp, 0, sizeof(sp));
        sp.cpuid = cpuid;
        sp.src_slabid = XMHFGEEC_SLAB_GEEC_PRIMESMP;
        sp.dst_slabid = XMHFGEEC_SLAB_XC_INIT;
        XMHF_SLAB_CALLNEW(&sp);
    }


    _XDPRINTF_("%s[%u,%u]: Should never be here. Halting!\n", __func__, (u16)cpuid, isbsp);
    HALT();

}



//////////////////////////////////////////////////////////////////////////////





/////////////////////////////////////////////////////////////////////
// setup base CPU data structures

//initialize GDT
static void __xmhfhic_x86vmx_initializeGDT(void){
		u32 i;

		for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
            TSSENTRY *t;
            u32 tss_base=(u32)&__xmhfhic_x86vmx_tss[i];

            //TSS descriptor
            t= (TSSENTRY *)&__xmhfhic_x86vmx_gdt_start[(__TRSEL/8)+(i*2)];
            t->attributes1= 0xE9;
            t->limit16_19attributes2= 0x0;
            t->baseAddr0_15= (u16)(tss_base & 0x0000FFFF);
            t->baseAddr16_23= (u8)((tss_base & 0x00FF0000) >> 16);
            t->baseAddr24_31= (u8)((tss_base & 0xFF000000) >> 24);
            t->limit0_15=0x67;
		}

}

//initialize IDT
static void __xmhfhic_x86vmx_initializeIDT(void){
	u32 i;

	for(i=0; i < EMHF_XCPHANDLER_MAXEXCEPTIONS; i++){
		__xmhfhic_x86vmx_idt_start[i].isrLow= (u16)__xmhfhic_exceptionstubs[i];
		__xmhfhic_x86vmx_idt_start[i].isrHigh= (u16) ( (u32)__xmhfhic_exceptionstubs[i] >> 16 );
		__xmhfhic_x86vmx_idt_start[i].isrSelector = __CS_CPL0;
		__xmhfhic_x86vmx_idt_start[i].count=0x0;
		__xmhfhic_x86vmx_idt_start[i].type=0xEE;	//32-bit interrupt gate
                                //present=1, DPL=11b, system=0, type=1110b
        //__xmhfhic_x86vmx_idt_start[i].offset3263=0;
        //__xmhfhic_x86vmx_idt_start[i].reserved=0;
	}

}


//initialize TSS
static void __xmhfhic_x86vmx_initializeTSS(void){
		u32 i;

		//initialize TSS descriptors for all CPUs
		for(i=0; i < xcbootinfo->cpuinfo_numentries; i++){
            tss_t *tss= (tss_t *)__xmhfhic_x86vmx_tss[i];
            /* x86_64
            tss->rsp0 = (u64) ( &__xmhfhic_x86vmx_tss_stack[i] + sizeof(__xmhfhic_x86vmx_tss_stack[0]) );
            */
            tss->esp0 = (u32) ( &__xmhfhic_x86vmx_tss_stack[i] + sizeof(__xmhfhic_x86vmx_tss_stack[0]) );
            tss->ss0 = __DS_CPL0;
		}
}


void xmhfhic_arch_setup_base_cpu_data_structures(void){

    //initialize GDT
    #if !defined(__XMHF_VERIFICATION__)
    __xmhfhic_x86vmx_initializeGDT();
    #endif

    //initialize IDT
    __xmhfhic_x86vmx_initializeIDT();

    //initialize TSS
    __xmhfhic_x86vmx_initializeTSS();

}









//////////////////////////////////////////////////////////////////////////////
// setup cpu state for hic












static bool __xmhfhic_x86vmx_setupvmxstate(u64 cpuid){
    u32 cpuindex = (u32)cpuid;
	const u32 vmx_msr_area_msrs[] = {MSR_EFER, MSR_IA32_PAT}; //critical MSRs that need to be saved/restored across guest VM switches
	const unsigned int vmx_msr_area_msrs_count = (sizeof(vmx_msr_area_msrs)/sizeof(vmx_msr_area_msrs[0]));	//count of critical MSRs that need to be saved/restored across VM switches
	u32 lodword, hidword;
	u64 vmcs_phys_addr = hva2spa(__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmcs_region);


	//save contents of VMX MSRs as well as MSR EFER and EFCR
	{
		u32 i;
		u32 eax, edx;
		for(i=0; i < IA32_VMX_MSRCOUNT; i++){
			rdmsr( (IA32_VMX_BASIC_MSR + i), &eax, &edx);
			__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[i] = (u64)edx << 32 | (u64) eax;
		}

		rdmsr(MSR_EFER, &eax, &edx);
		__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_efer = (u64)edx << 32 | (u64) eax;
		rdmsr(MSR_EFCR, &eax, &edx);
		__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_efcr = (u64)edx << 32 | (u64) eax;
  	}

 CASM_FUNCCALL(write_cr4, CASM_FUNCCALL(read_cr4,CASM_NOPARAM) |  CR4_VMXE);

#if !defined (__XMHF_VERIFICATION__)
	//enter VMX root operation using VMXON
	{
		u32 retval=0;
		u64 vmxonregion_paddr = hva2spa((void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmxon_region);
		//set VMCS rev id
		*((u32 *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmxon_region) = (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

        if(!__vmx_vmxon(vmxonregion_paddr)){
			_XDPRINTF_("%s(%u): unable to enter VMX root operation\n", __func__, (u32)cpuid);
			return false;
        }
	}

	//clear VMCS
	if(!__vmx_vmclear((u64)vmcs_phys_addr))
		return false;

	//set VMCS revision id
	*((u32 *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_vmcs_region) = (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_BASIC_MSR];

	//load VMPTR
	if(!__vmx_vmptrld((u64)vmcs_phys_addr))
		return false;
#endif //__XMHF_VERIFICATION__


	//setup host state
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CR0, CASM_FUNCCALL(read_cr0,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CR4, CASM_FUNCCALL(read_cr4,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CR3, CASM_FUNCCALL(read_cr3,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_CS_SELECTOR, CASM_FUNCCALL(read_segreg_cs,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_DS_SELECTOR, CASM_FUNCCALL(read_segreg_ds,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_ES_SELECTOR, CASM_FUNCCALL(read_segreg_es,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_FS_SELECTOR, CASM_FUNCCALL(read_segreg_fs,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_GS_SELECTOR, CASM_FUNCCALL(read_segreg_gs,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SS_SELECTOR, CASM_FUNCCALL(read_segreg_ss,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_TR_SELECTOR, CASM_FUNCCALL(read_tr_sel,CASM_NOPARAM));
	//_XDPRINTF_("%s: read_tr_sel = %08x\n", __func__, CASM_FUNCCALL(read_tr_sel,CASM_NOPARAM));
	//_XDPRINTF_("%s: HOST TR SELECTOR = %08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_HOST_TR_SELECTOR));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_GDTR_BASE, CASM_FUNCCALL(xmhf_baseplatform_arch_x86_getgdtbase,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_IDTR_BASE, CASM_FUNCCALL(xmhf_baseplatform_arch_x86_getidtbase,CASM_NOPARAM));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_TR_BASE, CASM_FUNCCALL(xmhf_baseplatform_arch_x86_gettssbase,CASM_NOPARAM));

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_RIP, _geec_sentinel_intercept_casmstub);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_RSP, CASM_FUNCCALL(read_rsp,CASM_NOPARAM));
	rdmsr(IA32_SYSENTER_CS_MSR, &lodword, &hidword);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SYSENTER_CS, lodword);
	rdmsr(IA32_SYSENTER_ESP_MSR, &lodword, &hidword);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SYSENTER_ESP, (((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_SYSENTER_EIP_MSR, &lodword, &hidword);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_SYSENTER_EIP, (((u64)hidword << 32) | (u64)lodword));
	rdmsr(IA32_MSR_FS_BASE, &lodword, &hidword);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_FS_BASE, (((u64)hidword << 32) | (u64)lodword) );
	rdmsr(IA32_MSR_GS_BASE, &lodword, &hidword);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_HOST_GS_BASE, (((u64)hidword << 32) | (u64)lodword) );

	//setup default VMX controls
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_PIN_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_CONTROLS, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_CONTROLS, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);

    /*
    x86_64
    //64-bit host
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_CONTROLS, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_EXIT_CONTROLS) | (1 << 9)) );
    */

	//IO bitmap support
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_iobitmap_region[0]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_IO_BITMAPA_ADDRESS_HIGH, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_iobitmap_region[1]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_IO_BITMAPB_ADDRESS_HIGH, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 25)) );

	//MSR bitmap support
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_MSR_BITMAPS_ADDRESS_FULL, hva2spa(__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrbitmaps_region ));
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 28)) );


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_PAGEFAULT_ERRORCODE_MASK, 0x00000000);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_PAGEFAULT_ERRORCODE_MATCH, 0x00000000);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EXCEPTION_BITMAP, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR3_TARGET_COUNT, 0);

	//activate secondary processor controls
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (u32) (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) | (u64)(1 << 31)) );

	//setup unrestricted guest
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 << 7)) );

	//setup VMCS link pointer
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_VMCS_LINK_POINTER_FULL, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_VMCS_LINK_POINTER_HIGH, 0xFFFFFFFFUL);

	//setup NMI intercept for core-quiescing
	//XXX: needs to go in xcinit/richguest slab
	//xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VMX_PIN_BASED, (u32)(xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_PIN_BASED) | (u64)(1 << 3) ) );

	//trap access to CR0 fixed 1-bits
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR0_MASK, (u32)(((((u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR] & ~(CR0_PE)) & ~(CR0_PG)) | CR0_CD) | CR0_NW) );

	//trap access to CR4 fixed bits (this includes the VMXE bit)
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR4_MASK, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR4_SHADOW, (u64)CR4_VMXE);

	//setup memory protection
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_SECCPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_SECCPU_BASED) | (u64)(1 <<1) | (u64)(1 << 5)) );
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VPID, 0); //[need to populate in sentinel]
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_FULL, 0); // [need to populate in sentinel]
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_EPT_POINTER_HIGH, 0); // [need to populate in sentinel]
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VMX_CPU_BASED, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VMX_CPU_BASED) & (u64)~(1 << 15) & (u64)~(1 << 16)) );

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR0, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR0_FIXED0_MSR]);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR0_SHADOW, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR0));

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR4, (u32)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msrs[INDEX_IA32_VMX_CR4_FIXED0_MSR]);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_EXCEPTION_ERRORCODE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_INTERRUPTION_INFORMATION, 0);


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RSP, 0); //[need to populate in sentinel]

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RIP, 0); // [need to populate in sentinel]
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ACTIVITY_STATE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_RFLAGS, (1 <<1) | (EFLAGS_IOPL));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_INTERRUPTIBILITY, 0);


    //IDTR
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_IDTR_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_IDTR_LIMIT, 0);



    //LDTR, unusable
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_LDTR_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_LDTR_LIMIT, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_LDTR_SELECTOR, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_LDTR_ACCESS_RIGHTS, 0x10000);



/*
    //64-bit specific guest slab setup
    {

        //Critical MSR load/store
        {
            u32 i;
            msr_entry_t *hmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region;
            msr_entry_t *gmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region;

            //store host and guest initial values of the critical MSRs
            for(i=0; i < vmx_msr_area_msrs_count; i++){
                u32 msr, eax, edx;
                msr = vmx_msr_area_msrs[i];
                rdmsr(msr, &eax, &edx);

                //host MSR values will be what we get from RDMSR
                hmsr[i].index = msr;
                hmsr[i].data = ((u64)edx << 32) | (u64)eax;

                //adjust and populate guest MSR values according to the MSR
                gmsr[i].index = msr;
                gmsr[i].data = ((u64)edx << 32) | (u64)eax;
                switch(msr){
                    case MSR_EFER:{
                        //gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_LME);
                        //gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_LMA);
                        //gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_SCE);
                        //gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_NXE);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_IA32_EFER_FULL, gmsr[i].data);

                    }
                    break;

                    default:
                        break;
                }

            }

            //host MSR load on exit, we store it ourselves before entry
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, hva2spa((void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

            //guest MSR load on entry, store on exit
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, hva2spa((void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, hva2spa((void*)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region));
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);

        }


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR4, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4) | CR4_PAE | CR4_PSE) );

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 9)) );
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 15)) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE0_FULL, _guestslab1_init_pdpt[0] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE1_FULL, _guestslab1_init_pdpt[1] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE2_FULL, _guestslab1_init_pdpt[2] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE3_FULL, _guestslab1_init_pdpt[3] );


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, &_guestslab1_init_pml4t );


        //TR, should be usable for VMX to work, but not used by guest
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_LIMIT, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_SELECTOR, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_ACCESS_RIGHTS, 0x8B);

        //CS, DS, ES, FS, GS and SS segments
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_SELECTOR, 0x8);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_ACCESS_RIGHTS, 0xa09b);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_ACCESS_RIGHTS, 0xa093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_ACCESS_RIGHTS, 0xa093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_ACCESS_RIGHTS, 0xa093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_ACCESS_RIGHTS, 0xa093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_ACCESS_RIGHTS, 0xa093);


        //GDTR
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_BASE, &_guestslab1_init_gdt_start);
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_GDTR_LIMIT, (sizeof(_guestslab1_init_gdt_start)-1) );


    }
*/

    //32-bit specific guest slab setup
    {

        //Critical MSR load/store
        {
            u32 i;
            msr_entry_t *hmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region;
            msr_entry_t *gmsr = (msr_entry_t *)__xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region;

            //store host and guest initial values of the critical MSRs
            for(i=0; i < vmx_msr_area_msrs_count; i++){
                u32 msr, eax, edx;
                msr = vmx_msr_area_msrs[i];
                rdmsr(msr, &eax, &edx);

                //host MSR values will be what we get from RDMSR
                hmsr[i].index = msr;
                hmsr[i].data = ((u64)edx << 32) | (u64)eax;

                //adjust and populate guest MSR values according to the MSR
                gmsr[i].index = msr;
                gmsr[i].data = ((u64)edx << 32) | (u64)eax;
                switch(msr){
                    case MSR_EFER:{
                        gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_LME);
                        gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_LMA);
                        gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_SCE);
                        gmsr[i].data = gmsr[i].data & (u64)~(1ULL << EFER_NXE);
                    }
                    break;

                    default:
                        break;
                }

            }

            //host MSR load on exit, we store it ourselves before entry
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_host_region);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_HIGH, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);

            //guest MSR load on entry, store on exit
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_HIGH, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_COUNT, vmx_msr_area_msrs_count);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL, __xmhfhic_x86vmx_archdata[cpuindex].vmx_msr_area_guest_region);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_HIGH, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_VM_EXIT_MSR_STORE_COUNT, vmx_msr_area_msrs_count);

        }


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR4, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR4) | CR4_PAE | CR4_PSE) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 9)) );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_CONTROL_VM_ENTRY_CONTROLS, (xmhfhw_cpu_x86vmx_vmread(VMCS_CONTROL_VM_ENTRY_CONTROLS) | (1 << 15)) );

        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE0_FULL, _guestslab1_init_pdpt[0] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE1_FULL, _guestslab1_init_pdpt[1] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE2_FULL, _guestslab1_init_pdpt[2] );
        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_PDPTE3_FULL, _guestslab1_init_pdpt[3] );


        //xmhfhw_cpu_x86vmx_vmwrite(VMCS_GUEST_CR3, &_guestslab1_init_pml4t );
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR3, 0 );


 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CR0, (xmhfhw_cpu_x86vmx_vmread(VMCS_GUEST_CR0) & ~(CR0_PG) ) );
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_CONTROL_CR0_SHADOW, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR0));

        //TR, should be usable for VMX to work, but not used by guest
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_LIMIT, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_SELECTOR, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_TR_ACCESS_RIGHTS, 0x8B);

        //CS, DS, ES, FS, GS and SS segments
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_SELECTOR, 0x8);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_CS_ACCESS_RIGHTS, 0xc09b);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_DS_ACCESS_RIGHTS, 0xc093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_ES_ACCESS_RIGHTS, 0xc093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_FS_ACCESS_RIGHTS, 0xc093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_GS_ACCESS_RIGHTS, 0xc093);

 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_SELECTOR, 0x10);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_BASE, 0);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_LIMIT, 0xFFFFFFFFUL);
 CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmwrite,VMCS_GUEST_SS_ACCESS_RIGHTS, 0xc093);



    }



















	/*_XDPRINTF_("%s: vmcs pinbased=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_PIN_BASED));
	_XDPRINTF_("%s: pinbase MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PINBASED_CTLS_MSR]);
	_XDPRINTF_("%s: cpu_based vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_CPU_BASED));
	_XDPRINTF_("%s: cpu_based MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS_MSR]);
	_XDPRINTF_("%s: seccpu_based vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VMX_SECCPU_BASED));
	_XDPRINTF_("%s: seccpu_based MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_PROCBASED_CTLS2_MSR]);
	_XDPRINTF_("%s: entrycontrols vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_ENTRY_CONTROLS));
	_XDPRINTF_("%s: entrycontrols MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_ENTRY_CTLS_MSR]);
	_XDPRINTF_("%s: exitcontrols vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_EXIT_CONTROLS));
	_XDPRINTF_("%s: exitcontrols MSR=%016llx\n", __func__, _cpustate_archdatavmx[context_desc.cpu_desc.cpu_index].vmx_msrs[INDEX_IA32_VMX_EXIT_CTLS_MSR]);
	_XDPRINTF_("%s: iobitmapa vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_IO_BITMAPA_ADDRESS_FULL));
	_XDPRINTF_("%s: iobitmapb vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_IO_BITMAPB_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap load vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_ENTRY_MSR_LOAD_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap store vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_EXIT_MSR_STORE_ADDRESS_FULL));
	_XDPRINTF_("%s: msrbitmap exit load vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_VM_EXIT_MSR_LOAD_ADDRESS_FULL));
	_XDPRINTF_("%s: ept pointer vmcs=%016llx\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_EPT_POINTER_FULL));
    */
	_XDPRINTF_("%s: CR0 vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR0));
	_XDPRINTF_("%s: CR4 vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_GUEST_CR4));
	_XDPRINTF_("%s: CR0 mask vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR0_MASK));
	_XDPRINTF_("%s: CR4 mask vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR4_MASK));
	_XDPRINTF_("%s: CR0 shadow vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR0_SHADOW));
	_XDPRINTF_("%s: CR4 shadow vmcs=%08x\n", __func__, CASM_FUNCCALL(xmhfhw_cpu_x86vmx_vmread,VMCS_CONTROL_CR4_SHADOW));


    return true;
}



void xmhf_hic_arch_setup_cpu_state(u64 cpuid){

	//replicate common MTRR state on this CPU
	#if !defined (__XMHF_VERIFICATION__)
	__xmhfhic_smp_cpu_x86_restorecpumtrrstate();
    #endif

    //load GDT
    //__xmhfhic_x86vmx_loadGDT(&__xmhfhic_x86vmx_gdt);

 CASM_FUNCCALL(xmhfhw_cpu_loadGDT,&__xmhfhic_x86vmx_gdt);
    _XDPRINTF_("%s[%u]: GDT loaded\n", __func__, (u32)cpuid);

 CASM_FUNCCALL(__xmhfhic_x86vmx_reloadCS,__CS_CPL0);
    _XDPRINTF_("%s[%u]: Reloaded CS\n", __func__, (u32)cpuid);

 CASM_FUNCCALL(__xmhfhic_x86vmx_reloadsegregs,__DS_CPL0);
    _XDPRINTF_("%s[%u]: Reloaded segment registers\n", __func__, (u32)cpuid);


    //load TR
 CASM_FUNCCALL(xmhfhw_cpu_loadTR, (__TRSEL + ((u32)cpuid * 16) ) );
    _XDPRINTF_("%s[%u]: TR loaded\n", __func__, (u32)cpuid);

    //load IDT
 CASM_FUNCCALL(xmhfhw_cpu_loadIDT,&__xmhfhic_x86vmx_idt);
    _XDPRINTF_("%s[%u]: IDT loaded\n", __func__, (u32)cpuid);

    ////turn on CR0.WP bit for supervisor mode write protection
    //write_cr0(read_cr0() | CR0_WP);
    //_XDPRINTF_("%s[%u]: Enabled supervisor mode write protection\n", __func__, (u32)cpuid);

    //set IOPL3
    __xmhfhic_x86vmx_setIOPL3(cpuid);
    _XDPRINTF_("%s[%u]: set IOPL to CPL-3\n", __func__, (u32)cpuid);


    //set LAPIC base address to preferred address
    {
        u64 msrapic = CASM_FUNCCALL(rdmsr64,MSR_APIC_BASE);
 CASM_FUNCCALL(wrmsr64,MSR_APIC_BASE, ((msrapic & 0x0000000000000FFFULL) | X86SMP_LAPIC_MEMORYADDRESS));
    }
    _XDPRINTF_("%s[%u]: set LAPIC base address to %016llx\n", __func__, (u32)cpuid, CASM_FUNCCALL(rdmsr64,MSR_APIC_BASE));

	//turn on NX protections
 CASM_FUNCCALL(wrmsr64,MSR_EFER, (rdmsr64(MSR_EFER) | (1 << EFER_NXE)) );
    _XDPRINTF_("%s[%u]: NX protections enabled\n", __func__, (u32)cpuid);


#if 0
	//enable PCIDE support
	{
 CASM_FUNCCALL(write_cr4,read_cr4() | CR4_PCIDE);
	}
    _XDPRINTF_("%s[%u]: PCIDE enabled\n", __func__, (u32)cpuid);
#endif

	//set OSXSAVE bit in CR4 to enable us to pass-thru XSETBV intercepts
	//when the CPU supports XSAVE feature
	if(xmhf_baseplatform_arch_x86_cpuhasxsavefeature()){
 CASM_FUNCCALL(write_cr4,read_cr4(CASM_NOPARAM) | CR4_OSXSAVE);
        _XDPRINTF_("%s[%u]: XSETBV passthrough enabled\n", __func__, (u32)cpuid);
	}


	//set bit 5 (EM) of CR0 to be VMX compatible in case of Intel cores
 CASM_FUNCCALL(write_cr0,read_cr0(CASM_NOPARAM) | 0x20);
    _XDPRINTF_("%s[%u]: Set CR0.EM to be VMX compatible\n", __func__, (u32)cpuid);


    //setup SYSENTER/SYSEXIT mechanism
    {
        wrmsr(IA32_SYSENTER_CS_MSR, __CS_CPL0, 0);
        wrmsr(IA32_SYSENTER_EIP_MSR, (u32)&_geec_sentinel_sysenter_casmstub, 0);
        wrmsr(IA32_SYSENTER_ESP_MSR, ((u32)_geec_primesmp_sysenter_stack[(u32)cpuid] + MAX_PLATFORM_CPUSTACK_SIZE), 0);
    }
    _XDPRINTF_("%s: setup SYSENTER/SYSEXIT mechanism\n", __func__);
    _XDPRINTF_("SYSENTER CS=%016llx\n", CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_CS_MSR));
    _XDPRINTF_("SYSENTER RIP=%016llx\n", CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_EIP_MSR));
    _XDPRINTF_("SYSENTER RSP=%016llx\n", CASM_FUNCCALL(rdmsr64,IA32_SYSENTER_ESP_MSR));


    //setup VMX state
    if(!__xmhfhic_x86vmx_setupvmxstate(cpuid)){
        _XDPRINTF_("%s[%u]: Unable to set VMX state. Halting!\n", __func__, (u32)cpuid);
        HALT();
    }
    _XDPRINTF_("%s[%u]: Setup VMX state\n", __func__, (u32)cpuid);

}



























/////
void slab_main(slab_params_t *sp){

    //setup base CPU data structures
    xmhfhic_arch_setup_base_cpu_data_structures();

    //setup SMP and move on to xmhfhic_smp_entry
    xmhfhic_arch_switch_to_smp();

    //we should never get here
    _XDPRINTF_("Should never be here. Halting!\n");
    HALT();

}
