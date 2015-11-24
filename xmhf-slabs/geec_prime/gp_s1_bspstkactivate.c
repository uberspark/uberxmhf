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



void gp_s1_bspstkactivate(void){
	u64 _msrefer;
	u32 _cr4;
	u32 _cr0 = (CR0_PE | CR0_PG | CR0_ET | CR0_EM);

	_msrefer = CASM_FUNCCALL(rdmsr64, MSR_EFER);
	_msrefer |= (1ULL << EFER_NXE);
	CASM_FUNCCALL(wrmsr64, MSR_EFER, (u32)_msrefer, (u32)((u64)_msrefer >> 32) );

        _XDPRINTF_("EFER=%016llx\n", CASM_FUNCCALL(rdmsr64,MSR_EFER));

	_cr4 = CASM_FUNCCALL(read_cr4, CASM_NOPARAM);
        _cr4 |= (CR4_PSE | CR4_PAE);
	CASM_FUNCCALL(write_cr4, _cr4);

        _XDPRINTF_("CR4=%08x\n", CASM_FUNCCALL(read_cr4,CASM_NOPARAM));

	CASM_FUNCCALL(write_cr3,(u32)&_xcprimeon_init_pdpt);

        _XDPRINTF_("CR3=%08x\n", CASM_FUNCCALL(read_cr3,CASM_NOPARAM));

	CASM_FUNCCALL(write_cr0, _cr0);

	gp_s1_hub();
}
