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

// EMHF x86 arch. specific configurable definitions
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_CONFIGX86_H__
#define __EMHF_CONFIGX86_H__

//======================================================================
//EMHF arch. specific configurable constant definitions

//runtime base address (virtual)
#define __TARGET_BASE					0xC0000000

//"sl" parameter block magic value
#define SL_PARAMETER_BLOCK_MAGIC		0xDEADBEEF

//"runtime" parameter block magic value
#define RUNTIME_PARAMETER_BLOCK_MAGIC	0xF00DDEAD

//16K stack for each core during runtime
#define RUNTIME_STACK_SIZE  			(16384)     

//8K stack for each core in "init"
#define INIT_STACK_SIZE					(8192)					

//max. cores/vcpus we support currently
#define MAX_MIDTAB_ENTRIES  			(4)
#define MAX_PCPU_ENTRIES  				(MAX_MIDTAB_ENTRIES)
#define MAX_VCPU_ENTRIES    			(MAX_PCPU_ENTRIES)

//maximum system memory map entries (e.g., E820) currently supported
#define MAX_E820_ENTRIES    			(64)  

//preferred TPM locality to use for access inside hypervisor
//needs to be 2 or 1 (4 is hw-only, 3 is sinit-only on Intel)
#define EMHF_TPM_LOCALITY_PREF 2

//where the guest OS boot record is loaded 
#define __GUESTOSBOOTMODULE_BASE		0x7c00
#define __GUESTOSBOOTMODULESUP1_BASE	0x7C00

//code segment of memory address where APs startup initially
//address 0x1000:0x0000 or 0x10000 physical
#define AP_BOOTSTRAP_CODE_SEG 			0x1000

//TXT SENTER MLE specific constants
#define TEMPORARY_HARDCODED_MLE_SIZE       0x10000
#define TEMPORARY_MAX_MLE_HEADER_SIZE      0x80
#define TEMPORARY_HARDCODED_MLE_ENTRYPOINT TEMPORARY_MAX_MLE_HEADER_SIZE

//VMX Unrestricted Guest (UG) E820 hook support
//we currently use the BIOS data area (BDA) unused region
//at 0x0040:0x00AC
#define	VMX_UG_E820HOOK_CS				(0x0040)	
#define	VMX_UG_E820HOOK_IP				(0x00AC)

// SHA-1 hash of runtime should be defined during build process.
// However, if it's not, don't fail.  Just proceed with all zeros.
// XXX TODO Disable proceeding with insecure hash value. 
#define BAD_INTEGRITY_HASH "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

#ifndef ___RUNTIME_INTEGRITY_HASH___
#define ___RUNTIME_INTEGRITY_HASH___ BAD_INTEGRITY_HASH
#endif // ___RUNTIME_INTEGRITY_HASH___ 

//======================================================================



#endif //__EMHF_CONFIGX86_H__
