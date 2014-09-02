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
 * XMHF core smp slab (xcsmp), x86-vmx-x86pc arch. backend
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-core.h>
#include <xmhf-debug.h>

#include <xcsmp.h>
#include <xcexhub.h>

static mtrr_state_t _mtrrs;
// platform cpu stacks
static u8 _cpustack[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE] __attribute__(( section(".stack") ));
static bool _ap_pmode_entry_with_paging(void) __attribute__((naked));
static void _xcsmp_cpu_x86_smpinitialize_commonstart(void);
// cpu table
static xc_cputable_t _cputable[MAX_PLATFORM_CPUS];
// count of platform cpus
static u32 _cpucount = 0;


__attribute__((naked)) static void _ap_bootstrap_code(void) {

    asm volatile (
           " .code32 \r\n"
           " movw %0, %%ax \r\n"
           " movw %%ax, %%ds \r\n"
           " movw %%ax, %%es \r\n"
           " movw %%ax, %%ss \r\n"
           " movw %%ax, %%fs \r\n"
           " movw %%ax, %%gs \r\n"

           " // set NX bit \r\n"
           " movl $0xc0000080, %%ecx \r\n"
           " rdmsr \r\n"
           " orl $(1 << 11), %%eax \r\n"
           " wrmsr \r\n"

           " movl %1, %%ebx \r\n"
           " movl (%%ebx), %%ebx \r\n"
           " movl %%ebx, %%cr3 \r\n"
           " movl %2, %%ebx \r\n"
           " movl (%%ebx), %%ebx \r\n"
           " movl %%ebx, %%cr4 \r\n"
           " movl %3, %%ebx \r\n"
           " movl (%%ebx), %%ebx \r\n"

           " movl %%cr0, %%eax \r\n"
           " orl $0x80000000, %%eax \r\n"
           " movl %%eax, %%cr0 \r\n"

           " jmpl *%%ebx \r\n"
           " hlt \r\n"
           " .balign 4096 \r\n"
            :
            : "i" (__DS_CPL0),
              "i" ((X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_cr3)),
              "i" ((X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_cr4)),
              "i" ((X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_entrypoint))
            :

        );
}



static void _xcsmp_cpu_x86_savecpumtrrstate(void){
	xmhfhw_cpu_x86_save_mtrrs(&_mtrrs);
}

static void _xcsmp_cpu_x86_restorecpumtrrstate(void){
	xmhfhw_cpu_x86_restore_mtrrs(&_mtrrs);
}


//wake up APs using the LAPIC by sending the INIT-SIPI-SIPI IPI sequence
static void _xcsmp_cpu_x86_wakeupAPs(void){
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
static void _xcsmp_container_vmx_wakeupAPs(void){
    static x86smp_apbootstrapdata_t apdata;

    apdata.ap_cr3 = read_cr3();
    apdata.ap_cr4 = read_cr4();
    apdata.ap_entrypoint = (u32)&_ap_pmode_entry_with_paging;
    apdata.ap_gdtdesc_limit = sizeof(apdata.ap_gdt) - 1;
    apdata.ap_gdtdesc_base = (X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_gdt);
    apdata.ap_cs_selector = __CS_CPL0;
    apdata.ap_cs_eip = (X86SMP_APBOOTSTRAP_CODESEG << 4);
    apdata.ap_gdtdesc16_limit = 0;
    apdata.ap_gdtdesc16_base = 0;
    apdata.ap_gdt[0] = 0x0000000000000000ULL;
    apdata.ap_gdt[1] = 0x00cf9a000000ffffULL;
    apdata.ap_gdt[2] = 0x00cf92000000ffffULL;

    _XDPRINTF_("%s: sizeof(apdata)=%u bytes\n", __FUNCTION__, sizeof(apdata));
    _XDPRINTF_("  apdata.ap_gdtdesc_limit at %08x\n", &apdata.ap_gdtdesc_limit);
    _XDPRINTF_("  apdata.ap_gdt at %08x\n", &apdata.ap_gdt);

    memcpy((void *)(X86SMP_APBOOTSTRAP_DATASEG << 4), (void *)&apdata, sizeof(apdata));

    memcpy((void *)(X86SMP_APBOOTSTRAP_CODESEG << 4), (void *)&_ap_bootstrap_code, PAGE_SIZE_4K);

#if defined (__DRT__)
    //step-2: wake up the APs sending the INIT-SIPI-SIPI sequence as per the
    //MP protocol. Use the APIC for IPI purposes.
    //if(!txt_is_launched()) { // XXX TODO: Do actual GETSEC[WAKEUP] in here?
    //    _XDPRINTF_("\nBSP: Using APIC to awaken APs...");
    //    _xcsmp_cpu_x86_wakeupAPs();
    //    _XDPRINTF_("\nBSP: APs should be awake.");
    //}else{
		//we ran SENTER, so do a GETSEC[WAKEUP]
        txt_heap_t *txt_heap;
        os_mle_data_t *os_mle_data;
        mle_join_t *mle_join;
        sinit_mle_data_t *sinit_mle_data;
        os_sinit_data_t *os_sinit_data;

        // sl.c unity-maps 0xfed00000 for 2M so these should work fine
        #ifndef __XMHF_VERIFICATION__
        txt_heap = get_txt_heap();
        //_XDPRINTF_("\ntxt_heap = 0x%08x", (u32)txt_heap);
        os_mle_data = get_os_mle_data_start(txt_heap);
        (void)os_mle_data;
        //_XDPRINTF_("\nos_mle_data = 0x%08x", (u32)os_mle_data);
        sinit_mle_data = get_sinit_mle_data_start(txt_heap);
        //_XDPRINTF_("\nsinit_mle_data = 0x%08x", (u32)sinit_mle_data);
        os_sinit_data = get_os_sinit_data_start(txt_heap);
        //_XDPRINTF_("\nos_sinit_data = 0x%08x", (u32)os_sinit_data);
	#endif

        // Start APs.  Choose wakeup mechanism based on
        // capabilities used. MLE Dev Guide says MLEs should
        // support both types of Wakeup mechanism.

        // We are jumping straight into the 32-bit portion of the
        // unity-mapped trampoline that starts at 64K
        // physical. Without SENTER, or with AMD, APs start in
        // 16-bit mode.  We get to skip that.
        //_XDPRINTF_("\nBSP: _mle_join_start = 0x%08x, _ap_bootstrap_start = 0x%08x",
		//	(u32)_mle_join_start, (u32)_ap_bootstrap_start);
        //_XDPRINTF_("\nBSP: _ap_bootstrap_blob_mle_join_start = 0x%08x, _ap_bootstrap_blob = 0x%08x",
		//	(u32)_ap_bootstrap_blob_mle_join_start, (u32)_ap_bootstrap_blob);

        // enable SMIs on BSP before waking APs (which will enable them on APs)
        // because some SMM may take immediate SMI and hang if AP gets in first
        //_XDPRINTF_("Enabling SMIs on BSP\n");
        //__getsec_smctrl();

        #ifndef __XMHF_VERIFICATION__
        //mle_join = (mle_join_t*)((u32)_ap_bootstrap_blob_mle_join_start - (u32)_ap_bootstrap_blob + 0x10000); // XXX magic number
        mle_join = (mle_join_t *)((u32)(X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_gdtdesc_limit));
        #endif

        _XDPRINTF_("\nBSP: mle_join.gdt_limit = %x", mle_join->gdt_limit);
        _XDPRINTF_("\nBSP: mle_join.gdt_base = %x", mle_join->gdt_base);
        _XDPRINTF_("\nBSP: mle_join.seg_sel = %x", mle_join->seg_sel);
        _XDPRINTF_("\nBSP: mle_join.entry_point = %x", mle_join->entry_point);

	#ifndef __XMHF_VERIFICATION__
        write_priv_config_reg(TXTCR_MLE_JOIN, (uint64_t)(unsigned long)mle_join);

        if (os_sinit_data->capabilities.rlp_wake_monitor) {
            _XDPRINTF_("\nBSP: joining RLPs to MLE with MONITOR wakeup");
            _XDPRINTF_("\nBSP: rlp_wakeup_addr = 0x%x", sinit_mle_data->rlp_wakeup_addr);
            *((uint32_t *)(unsigned long)(sinit_mle_data->rlp_wakeup_addr)) = 0x01;
        }else {
            _XDPRINTF_("\nBSP: joining RLPs to MLE with GETSEC[WAKEUP]");
            __getsec_wakeup();
            _XDPRINTF_("\nBSP: GETSEC[WAKEUP] completed");
        }
	#endif


	//}

#else //!__DRT__

        _XDPRINTF_("\nBSP: Using APIC to awaken APs...");
        _xcsmp_cpu_x86_wakeupAPs();
        _XDPRINTF_("\nBSP: APs should be awake.");

#endif


}

//return 1 if the calling CPU is the BSP
static bool _xcsmp_cpu_x86_isbsp(void){
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
static void _xcsmp_cpu_x86_smpinitialize_commonstart(void){
	u32 cpuid = xmhf_baseplatform_arch_x86_getcpulapicid();
	bool is_bsp = _xcsmp_cpu_x86_isbsp();
	u32 bcr0;

	//initialize base CPU state
	xmhfhw_cpu_initialize();

	//replicate common MTRR state on this CPU
	_xcsmp_cpu_x86_restorecpumtrrstate();

	//set bit 5 (EM) of CR0 to be VMX compatible in case of Intel cores
	bcr0 = read_cr0();
	bcr0 |= 0x20;
	write_cr0(bcr0);

	//load TR
	{
	  u32 gdtstart = (u32)xmhf_baseplatform_arch_x86_getgdtbase();
	  u16 trselector = 	__TRSEL;
	  asm volatile("movl %0, %%edi\r\n"
		"xorl %%eax, %%eax\r\n"
		"movw %1, %%ax\r\n"
		"addl %%eax, %%edi\r\n"		//%edi is pointer to TSS descriptor in GDT
		"addl $0x4, %%edi\r\n"		//%edi points to top 32-bits of 64-bit TSS desc.
		"lock andl $0xFFFF00FF, (%%edi)\r\n"
		"lock orl  $0x00008900, (%%edi)\r\n"
		"ltr %%ax\r\n"				//load TR
	     :
	     : "m"(gdtstart), "m"(trselector)
	     : "edi", "eax"
	  );
	}


	_XDPRINTF_("\n%s: cpu %x, isbsp=%u, Proceeding to call init_entry...\n", __FUNCTION__, cpuid, is_bsp);

	if( XMHF_SLAB_CALL(xcrichguest_entry(cpuid, is_bsp)) ){
		_XDPRINTF_("%s: Fatal. Should never be here. Halting!\n", __FUNCTION__);
		HALT();
	}
}



static bool _ap_pmode_entry_with_paging(void) __attribute__((naked)){

    asm volatile(	"lgdt %0\r\n"
					"lidt %1\r\n"
					"mov %2, %%ecx\r\n"
					"rdmsr\r\n"
					"andl $0xFFFFF000, %%eax\r\n"
					"addl $0x20, %%eax\r\n"
					"movl (%%eax), %%eax\r\n"
					"shr $24, %%eax\r\n"
					"movl %3, %%edx\r\n"
					"movl %4, %%ebx\r\n"
					"xorl %%ecx, %%ecx\r\n"
					"xorl %%edi, %%edi\r\n"
					"getidxloop:\r\n"
					"movl 0x0(%%ebx, %%edi), %%ebp\r\n"  	//ebp contains the lapic id
					"cmpl %%eax, %%ebp\r\n"
					"jz gotidx\r\n"
					"incl %%ecx\r\n"
					"addl %5, %%edi\r\n"
					"cmpl %%edx, %%ecx\r\n"
					"jb getidxloop\r\n"
					"hlt\r\n"								//we should never get here, if so just halt
					"gotidx:\r\n"							// ecx contains index into g_xc_cputable
					"movl 0x4(%%ebx, %%edi), %%eax\r\n"	 	// eax = g_xc_cputable[ecx].cpu_index
					"movl %6, %%edi \r\n"					// edi = &_cpustack
					"movl %7, %%ecx \r\n"					// ecx = sizeof(_cpustack[0])
					"mull %%ecx \r\n"						// eax = sizeof(_cpustack[0]) * eax
					"addl %%ecx, %%eax \r\n"				// eax = (sizeof(_cpustack[0]) * eax) + sizeof(_cpustack[0])
					"addl %%edi, %%eax \r\n"				// eax = &_cpustack + (sizeof(_cpustack[0]) * eax) + sizeof(_cpustack[0])
					"movl %%eax, %%esp \r\n"				// esp = top of stack for the cpu
					:
					: "m" (_gdt), "m" (_idt), "i" (MSR_APIC_BASE), "m" (_cpucount), "i" (&_cputable), "i" (sizeof(xc_cputable_t)), "i" (&_cpustack), "i" (sizeof(_cpustack[0]))
	);

	_xcsmp_cpu_x86_smpinitialize_commonstart();

}

//======================================================================

//re-initialize DMA protections (if needed) for the runtime
bool xcsmp_arch_dmaprot_reinitialize(void){
	//we don't need to reinitialize DMA protections since we setup
	//VT-d PMRs in the secure loader
	return true;
}


//initialize SMP
bool xcsmp_arch_smpinitialize(void){
	u32 i;

	_cpucount = xcbootinfo->cpuinfo_numentries;

	//initialize cpu table
	for(i=0; i < _cpucount; i++){
			_cputable[i].cpuid = xcbootinfo->cpuinfo_buffer[i].lapic_id;
			_cputable[i].cpu_index = i;
	}

	//save cpu MTRR state which we will later replicate on all APs
	_xcsmp_cpu_x86_savecpumtrrstate();

	//signal that basic base platform data structure initialization is complete
	//(used by the exception handler component)
	//g_bplt_initiatialized = true;

	//wake up APS
	if(_cpucount > 1){
	  _xcsmp_container_vmx_wakeupAPs();
	}


	//fall through to common code
	_XDPRINTF_("\nRelinquishing BSP thread and moving to common...");
	if( _ap_pmode_entry_with_paging() ){
		_XDPRINTF_("\nBSP must never get here. HALT!");
		HALT();
	}
}
