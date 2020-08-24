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

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
// #include <xmhfgeec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec_prime.h>


#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
	uint32_t check_esp, check_eip = CASM_RET_EIP;

	void hwm_vdriver_writeesp(uint32_t oldval, uint32_t newval){
		//@assert (newval >= ((uint32_t)&_init_bsp_cpustack + 4)) && (newval <= ((uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE)) ;
	}

	void hwm_vdriver_cpu_writecr3(uint32_t oldval, uint32_t newval){
		//@assert 0;
	}

	void hwm_vdriver_txt_write_rlp_wakeup_addr(uint32_t oldval, uint32_t newval){
		x86smp_apbootstrapdata_t *apdata = (x86smp_apbootstrapdata_t *)&hwm_mem_region_apbootstrap_dataseg;

		if(newval != 0){
			//@assert (hwm_txt_mle_join_hi == 0);
			//@assert (hwm_txt_mle_join_lo == ((uint32_t)(X86SMP_APBOOTSTRAP_DATASEG << 4) + 16));
			//@assert (apdata->ap_eip == (X86SMP_APBOOTSTRAP_CODESEG << 4));
		}
	}

	void hwm_vdriver_mem_copy_to_apbootstrap_codeseg(uint32_t sourceaddr){
		//@assert (sourceaddr == (uint32_t)&gp_s4_entry);
	}

	void main(void){
		//populate hardware model stack and program counter
		hwm_cpu_gprs_esp = (uint32_t)&_init_bsp_cpustack + MAX_PLATFORM_CPUSTACK_SIZE;
		hwm_cpu_gprs_eip = check_eip;
		check_esp = hwm_cpu_gprs_esp; // pointing to top-of-stack

		//execute harness
		gp_s3_startcores();

		//@assert hwm_cpu_gprs_esp == check_esp;
		//@assert hwm_cpu_gprs_eip == check_eip;
	}
#endif // __XMHF_VERIFICATION__

//start all cores
void gp_s3_startcores(void){
        txt_heap_t *txt_heap;
        mle_join_t *mle_join;
        sinit_mle_data_t sinit_mle_data;
        os_sinit_data_t os_sinit_data;

	//populate apdata structure
	apdata.ap_cr3 = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr3,CASM_NOPARAM);
	apdata.ap_cr4 = CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__read_cr4,CASM_NOPARAM);
	apdata.ap_entrypoint = (uint32_t)&gp_s4_apstacks;
	apdata.ap_gdtdesc_limit = sizeof(apdata.ap_gdt) - 1;
	apdata.ap_gdtdesc_base = (X86SMP_APBOOTSTRAP_DATASEG << 4) + 48;
	apdata.ap_cs_selector = __CS_CPL0;
	apdata.ap_eip = (X86SMP_APBOOTSTRAP_CODESEG << 4);
	apdata.ap_gdt[0] = 0x0000000000000000ULL;
	apdata.ap_gdt[1] = 0x00cf9a000000ffffULL;
	apdata.ap_gdt[2] = 0x00cf92000000ffffULL;

	//_XDPRINTF_("%s: sizeof(apdata)=%u bytes\n", __func__, sizeof(apdata));
	//_XDPRINTF_("  apdata.ap_gdtdesc_limit at %08x\n", &apdata.ap_gdtdesc_limit);
	//_XDPRINTF_("  apdata.ap_gdt at %08x\n", &apdata.ap_gdt);

	//copy apdata to X86SMP_APBOOTSTRAP_DATASEG
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmem_copy_obj2sys, (uint32_t)(X86SMP_APBOOTSTRAP_DATASEG << 4),
						(void *)&apdata, sizeof(apdata));

	//copy AP entry code to X86SMP_APBOOTSTRAP_CODESEG
	CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmem_copy_obj2sys, (uint32_t)(X86SMP_APBOOTSTRAP_CODESEG << 4),
		(void *)&gp_s4_entry, PAGE_SIZE_4K);


	//grab sinit2mle and os2sinit data structures from TXT heap
        txt_heap = uberspark_uobjrtl_hw__generic_x86_32_intel__get_txt_heap();
        CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmem_copy_sys2obj, &sinit_mle_data,
		get_sinit_mle_data_start(txt_heap, (uint32_t)uberspark_uobjrtl_hw__generic_x86_32_intel__read_pub_config_reg(TXTCR_HEAP_SIZE)),
		sizeof(sinit_mle_data_t));

        CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmem_copy_sys2obj, &os_sinit_data,
		get_os_sinit_data_start(txt_heap, (uint32_t)uberspark_uobjrtl_hw__generic_x86_32_intel__read_pub_config_reg(TXTCR_HEAP_SIZE)),
		sizeof(os_sinit_data_t));


        // enable SMIs on BSP before waking APs (which will enable them on APs)
        // because some SMM may take immediate SMI and hang if AP gets in first
        //_XDPRINTF_("Enabling SMIs on BSP\n");
        //__getsec_smctrl();

	//get a pointer to the mle_join data structure within apdata
        mle_join = (mle_join_t *)((uint32_t)(X86SMP_APBOOTSTRAP_DATASEG << 4) + 16);

        _XDPRINTF_("\nBSP: mle_join.gdt_limit = %x", mle_join->gdt_limit);
        _XDPRINTF_("\nBSP: mle_join.gdt_base = %x", mle_join->gdt_base);
        _XDPRINTF_("\nBSP: mle_join.seg_sel = %x", mle_join->seg_sel);
        _XDPRINTF_("\nBSP: mle_join.entry_point = %x", mle_join->entry_point);

        //populate TXT MLE_JOIN register
        write_priv_config_reg(TXTCR_MLE_JOIN, (uint64_t)(unsigned long)mle_join);


	//wakeup APs
        if (os_sinit_data.capabilities & TXT_CAPS_T_RLP_WAKE_MONITOR) {
            _XDPRINTF_("BSP: joining RLPs to MLE with MONITOR wakeup\n");
            _XDPRINTF_("BSP: rlp_wakeup_addr=0x%08x\n", sinit_mle_data.rlp_wakeup_addr);
	    CASM_FUNCCALL(uberspark_uobjrtl_hw__generic_x86_32_intel__sysmemaccess_writeu32, sinit_mle_data.rlp_wakeup_addr, 0x01);
        }else {
            _XDPRINTF_("BSP: joining RLPs to MLE with GETSEC[WAKEUP]\n");
            __getsec_wakeup();
            _XDPRINTF_("BSP: GETSEC[WAKEUP] completed\n");
        }

}


