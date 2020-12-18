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
 GEEC sentinel low-level support routines
 author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf.h>
#include <uberspark/hwm/include/arch/x86_32/intel/hwm.h>
// #include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/xmhf-debug.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/geec.h>

#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc_ihub.h>

#if defined (__XMHF_VERIFICATION__) && defined (__USPARK_FRAMAC_VA__)
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc.h>
#include <uberspark/uobjcoll/platform/pc/uxmhf/main/include/uobjs/xc_ihub.h>

uint32_t check_eip = CASM_RET_EIP;
uint32_t cpuid = 0;	//cpu

void hwm_vdriver_slabep(void){
	//@assert hwm_cpu_gprs_eip == (uint32_t)xmhfgeec_slab_info_table[XMHFGEEC_SLAB_XC_IHUB].entrystub;
	//@assert false;
}

void drv_path_callicpt(void){
	//invoke sentinel intercept stub
	CASM_FUNCCALL(gs_entry_icptstub, CASM_NOPARAM);
	//@assert false;
}

void main(void){
	//populate hardware model stack and program counter
	hwm_cpu_gprs_esp = _slab_tos[cpuid];
	hwm_cpu_gprs_eip = check_eip;
	drv_path_callicpt();
}
#endif
////// intercept entry point
CASM_FUNCDEF(void, xcihub_entry_icptstub,
{
    __casm__pushal();
    __casm__pushl_esp();
    __casm__call_c_1p(xcihub_entry_icpt, x86regs_t *);
    __casm__hlt();
},
void *noparam)




