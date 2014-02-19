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

/*
 * XMHF core API calls that hypapps rely on
 * 
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

COREAPIXMHFCPUTS xmhfcore_outputdebugstring = NULL;

COREAPIXMHFBASEPLATFORMREBOOT xmhfcore_reboot = NULL;

COREAPIXMHFSETMEMPROT xmhfcore_setmemprot = NULL;

COREAPIXMHFMEMPROTGETPROT xmhfcore_memprot_getprot = NULL;

COREAPIXMHFMEMPROTFLUSHMAPPINGS xmhfcore_memprot_flushmappings = NULL;

COREAPIXMHFSMPGUESTWALKPAGETABLES xmhfcore_smpguest_walk_pagetables = NULL;

COREAPIXMHFPARTITIONLEGACYIOSETPROT xmhfcore_partition_legacyIO_setprot = NULL;

COREAPIXMHFBASEPLATFORMARCHX86ACPIGETRSDP xmhfcore_baseplatform_arch_x86_acpi_getRSDP = NULL;

COREAPIXMHFTPMOPENLOCALITY xmhfcore_tpm_open_locality = NULL;

COREAPIXMHFTPMDEACTIVATEALLLOCALITIES xmhfcore_tpm_deactivate_all_localities = NULL;

COREAPIXMHFTPMWRITECMDFIFO xmhfcore_tpm_write_cmd_fifo = NULL;

COREAPIXMHFMEMPROTARCHX86SVMGETHCR3 xmhfcore_memprot_arch_x86svm_get_h_cr3 = NULL;

COREAPIXMHFMEMPROTARCHX86SVMSETHCR3 xmhfcore_memprot_arch_x86svm_set_h_cr3 = NULL;

COREAPIXMHFMEMPROTARCHX86VMXGETEPTP xmhfcore_memprot_arch_x86vmx_get_EPTP = NULL;

COREAPIXMHFMEMPROTARCHX86VMXSETEPTP xmhfcore_memprot_arch_x86vmx_set_EPTP = NULL;

COREAPIXMHFBASEPLATFORMGETCPUTABLE xmhfcore_baseplatform_getcputable = NULL;

//the table of core API pointers
u32 lxc_swfp_tablecoreapipointers[] = {
		&xmhfcore_outputdebugstring,
		&xmhfcore_reboot,
		&xmhfcore_setmemprot,
		&xmhfcore_memprot_getprot,
		&xmhfcore_memprot_flushmappings,
		&xmhfcore_smpguest_walk_pagetables,
		&xmhfcore_partition_legacyIO_setprot,
		&xmhfcore_baseplatform_arch_x86_acpi_getRSDP,
		&xmhfcore_tpm_open_locality,
		&xmhfcore_tpm_deactivate_all_localities,
		&xmhfcore_tpm_write_cmd_fifo,
		&xmhfcore_memprot_arch_x86svm_get_h_cr3,
		&xmhfcore_memprot_arch_x86svm_set_h_cr3,
		&xmhfcore_memprot_arch_x86vmx_get_EPTP,
		&xmhfcore_memprot_arch_x86vmx_set_EPTP,
		&xmhfcore_baseplatform_getcputable,
		0
};

