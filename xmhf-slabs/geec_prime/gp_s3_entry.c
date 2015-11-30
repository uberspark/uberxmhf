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

#include <xmhf.h>
#include <xmhf-debug.h>

#include <xmhfgeec.h>

#include <geec_prime.h>
#include <geec_sentinel.h>
#include <uapi_slabmempgtbl.h>
#include <xc_init.h>

static void __xmhfhic_smp_cpu_x86_wakeupAPs(void);
static void __xmhfhic_smp_container_vmx_wakeupAPs(void);
//static u64 _xcsmp_ap_entry_lock = 1;
static u64 _ap_cr3=0;


//wake up APs using the LAPIC by sending the INIT-SIPI-SIPI IPI sequence
static void __xmhfhic_smp_cpu_x86_wakeupAPs(void){
	u32 eax, edx;
	volatile u32 *icr;
	u64 msr_value;

	//read LAPIC base address from MSR
       	msr_value = CASM_FUNCCALL(rdmsr64, MSR_APIC_BASE);
	eax = (u32)msr_value;
	edx = (u32)(msr_value >> 32);

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
    apdata.ap_entrypoint = (u32)&gp_s4_apstacks;
    apdata.ap_gdtdesc_limit = sizeof(apdata.ap_gdt) - 1;
    //apdata.ap_gdtdesc_base = (X86SMP_APBOOTSTRAP_DATASEG << 4) + offsetof(x86smp_apbootstrapdata_t, ap_gdt);
    apdata.ap_gdtdesc_base = (X86SMP_APBOOTSTRAP_DATASEG << 4) + 48;
    apdata.ap_cs_selector = __CS_CPL0;
    apdata.ap_eip = (X86SMP_APBOOTSTRAP_CODESEG << 4);
    //apdata.cpuidtable = (u32)&__xmhfhic_x86vmx_cpuidtable;
    apdata.ap_gdt[0] = 0x0000000000000000ULL;
    apdata.ap_gdt[1] = 0x00cf9a000000ffffULL;
    apdata.ap_gdt[2] = 0x00cf92000000ffffULL;

    _XDPRINTF_("%s: sizeof(apdata)=%u bytes\n", __func__, sizeof(apdata));
    _XDPRINTF_("  apdata.ap_gdtdesc_limit at %08x\n", &apdata.ap_gdtdesc_limit);
    _XDPRINTF_("  apdata.ap_gdt at %08x\n", &apdata.ap_gdt);

    memcpy((void *)(X86SMP_APBOOTSTRAP_DATASEG << 4), (void *)&apdata, sizeof(apdata));

    memcpy((void *)(X86SMP_APBOOTSTRAP_CODESEG << 4), (void *)&gp_s4_entry, PAGE_SIZE_4K);

#if defined (__DRT__)
    {
        txt_heap_t *txt_heap;
        //os_mle_data_t *os_mle_data;
        mle_join_t *mle_join;
        //sinit_mle_data_t sinit_mle_data;
        os_sinit_data_t os_sinit_data;

        txt_heap = get_txt_heap();
        //os_mle_data = get_os_mle_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE));
        //xmhfhw_sysmemaccess_copy(&sinit_mle_data,
	//	get_sinit_mle_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)),
	//	sizeof(sinit_mle_data_t));
        xmhfhw_sysmemaccess_copy(&os_sinit_data,
		get_os_sinit_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)),
		sizeof(os_sinit_data_t));

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

        if (os_sinit_data.capabilities & TXT_CAPS_T_RLP_WAKE_MONITOR) {
            _XDPRINTF_("\nBSP: joining RLPs to MLE with MONITOR wakeup");
            //_XDPRINTF_("\nBSP: rlp_wakeup_addr = 0x%x", sinit_mle_data.rlp_wakeup_addr);
            // *((uint32_t *)(unsigned long)(sinit_mle_data.rlp_wakeup_addr)) = 0x01;
	    xmhfhw_sysmemaccess_writeu32(
		(get_sinit_mle_data_start(txt_heap, (uint32_t)read_pub_config_reg(TXTCR_HEAP_SIZE)) + offsetof(sinit_mle_data_t, rlp_wakeup_addr) ),
					0x01);


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



void gp_s3_entry(void){

	//switch to prime page tables
	_XDPRINTF_("Proceeding to switch to GEEC_PRIME pagetables...\n");
	//CASM_FUNCCALL(write_cr3,(u32)xmhfgeec_slab_info_table[XMHFGEEC_SLAB_GEEC_PRIME].mempgtbl_cr3);
	CASM_FUNCCALL(write_cr3,(u32)&gp_rwdatahdr.gp_vhslabmempgtbl_lvl4t);
	_XDPRINTF_("Switched to GEEC_PRIME pagetables...\n");


	//save cpu MTRR state which we will later replicate on all APs
	xmhfhw_cpu_x86_save_mtrrs(&_mtrrs);

	//save page table base which we will later replicate on all APs
	_ap_cr3 = CASM_FUNCCALL(read_cr3,CASM_NOPARAM);

	//wake up APS
	if(xcbootinfo->cpuinfo_numentries > 1){
	  __xmhfhic_smp_container_vmx_wakeupAPs();
	}

	//fall through to common code
	_XDPRINTF_("%s: Relinquishing BSP thread and moving to common...\n", __func__);
	gp_s4_s6_entry();

	//we should never get here
	_XDPRINTF_("%s:%u: Must never get here. Halting\n", __func__, __LINE__);
	HALT();


}










