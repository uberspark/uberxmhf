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
 sentinel exception entry point
 author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/hwm/include/arch/x86_32/intel/hwm.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_exhub.h>

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xc_exhub.h>

uint32_t saved_cpu_gprs_ebx=0;
uint32_t saved_cpu_gprs_esi=0;
uint32_t saved_cpu_gprs_edi=0;
uint32_t saved_cpu_gprs_ebp=0;
uint32_t cpuid = 0;	//cpu

void cabi_establish(void){
	hwm_cpu_gprs_ebx = 5UL;
	hwm_cpu_gprs_esi = 6UL;
	hwm_cpu_gprs_edi = 7UL;
	saved_cpu_gprs_ebx = hwm_cpu_gprs_ebx;
	saved_cpu_gprs_esi = hwm_cpu_gprs_esi;
	saved_cpu_gprs_edi = hwm_cpu_gprs_edi;
}

void cabi_check(void){
	//@ assert saved_cpu_gprs_ebx == hwm_cpu_gprs_ebx;
	//@ assert saved_cpu_gprs_esi == hwm_cpu_gprs_esi;
	//@ assert saved_cpu_gprs_edi == hwm_cpu_gprs_edi;
}

uint32_t check_esp, check_eip = CASM_RET_EIP;

	#if defined (DRV_PATH_CALLEXCP)
	x86vmx_exception_frame_t drv_path_callexcp_excpframe;
	
	void hwm_vdriver_slabep(void){
		//@assert hwm_cpu_gprs_eip == (uint32_t)xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_EXHUB].entrystub;
		//@assert false;
	}
	
	void drv_path_callexcp(void){
		hwm_cpu_gprs_esp -= sizeof(x86vmx_exception_frame_t);
	
		//invoke sentinel exception stub
		CASM_FUNCCALL(__xmhf_exception_handler_8, CASM_NOPARAM);
		//@assert false;
	}
	#endif // defined


void main(void){
	//populate hardware model stack and program counter
	hwm_cpu_gprs_esp = _slab_tos[cpuid];
	hwm_cpu_gprs_eip = check_eip;
	check_esp = hwm_cpu_gprs_esp; // pointing to top-of-stack

	#if defined (DRV_PATH_CALLEXCP)
	drv_path_callexcp();
	#endif // DRV_PATH_CALLEXCP

}

#endif
////// exceptions entry stubs

#define XMHF_EXCEPTION_HANDLER_DEFINE(vector) 												\
	CASM_FUNCDEF(void, __xmhf_exception_handler_##vector, 					\
    { \
        __casm__pushl_imm(vector); \
        __casm__pushal(); \
        MACRO_EXPANSION_WORKAROUND(__casm__movw_imm_ax,__DS_CPL0); \
        __casm__movw_ax_ds();\
        __casm__movw_ax_es();\
        __casm__pushl_esp(); \
	__casm__call_c_1p(xcexhub_entryexcp,x86vmx_exception_frame_t *); \
        __casm__hlt(); \
    },\
    void *noparam) \

#define XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(vector) 												\
	CASM_FUNCDEF(void, __xmhf_exception_handler_##vector, 					\
    {\
		__casm__pushl_imm(0x0); \
        __casm__pushl_imm(vector); \
        __casm__pushal(); \
        MACRO_EXPANSION_WORKAROUND(__casm__movw_imm_ax,__DS_CPL0); \
        __casm__movw_ax_ds();\
        __casm__movw_ax_es();\
        __casm__pushl_esp(); \
        __casm__call_c_1p(xcexhub_entryexcp,x86vmx_exception_frame_t *); \
        __casm__hlt(); \
    },\
    void *noparam) \



XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(0)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(1)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(2)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(3)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(4)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(5)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(6)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(7)
XMHF_EXCEPTION_HANDLER_DEFINE(8)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(9)
XMHF_EXCEPTION_HANDLER_DEFINE(10)
XMHF_EXCEPTION_HANDLER_DEFINE(11)
XMHF_EXCEPTION_HANDLER_DEFINE(12)
XMHF_EXCEPTION_HANDLER_DEFINE(13)
XMHF_EXCEPTION_HANDLER_DEFINE(14)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(15)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(16)
XMHF_EXCEPTION_HANDLER_DEFINE(17)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(18)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(19)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(20)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(21)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(22)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(23)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(24)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(25)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(26)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(27)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(28)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(29)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(30)
XMHF_EXCEPTION_HANDLER_DEFINE_WITHERRORCODE(31)





