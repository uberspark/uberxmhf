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

// XMHF platform/arch configuration header
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_CONFIG_H__
#define __XMHF_CONFIG_H__

//"runtime" parameter block magic value
#define RUNTIME_PARAMETER_BLOCK_MAGIC	0xF00DDEAD

#define SL_PARAMETER_BLOCK_MAGIC		0xF00DDEAD

//16K stack for each core during runtime
#define RUNTIME_STACK_SIZE  			(16384)

//8K stack for each core in "init"
#define INIT_STACK_SIZE					(8192)

//max. size of command line parameter buffer
#define MAX_CMDLINE_BUFFER_SIZE			(128)

//max. cores/vcpus we support currently
#ifndef __XMHF_VERIFICATION__
	#define	MAX_PLATFORM_CPUS					(8)
#else
	#define	MAX_PLATFORM_CPUS					(1)
#endif

//max. platform devices we support currently
#define MAX_PLATFORM_DEVICES                    (64)

#define MAX_MIDTAB_ENTRIES  			(MAX_PLATFORM_CPUS)
#define MAX_PCPU_ENTRIES  				(MAX_PLATFORM_CPUS)
#define MAX_VCPU_ENTRIES    			(MAX_PLATFORM_CPUS)

//max. primary partitions we support
#define	MAX_PRIMARY_PARTITIONS					(1)

//max. secondary partitions we support
#define	MAX_SECONDARY_PARTITIONS				(4)

//max. size of primary partition HPT data buffer
#define	MAX_PRIMARY_PARTITION_HPTDATA_SIZE				(2054*4096)

//max. size of primary partition HPT data buffer
#define	MAX_SECONDARY_PARTITION_HPTDATA_SIZE			(6*4096)

//max. partition trapmask data buffer
#define MAX_PRIMARY_PARTITION_TRAPMASKDATA_SIZE					(4*4096)

//max. size of CPU arch. specific data (32K default)
#define	MAX_PLATFORM_CPUARCHDATA_SIZE			(8*4096)

//max. size of CPU stack (16K default)
#define MAX_PLATFORM_CPUSTACK_SIZE				(4*4096)

//max. number of arch. specific parameters for hypapp callback
#define MAX_XC_HYPAPP_CB_ARCH_PARAMS	8

//maximum system memory map entries (e.g., E820) currently supported
#define MAX_E820_ENTRIES    			(64)

// SHA-1 hash of runtime should be defined during build process.
// However, if it's not, don't fail.  Just proceed with all zeros.
// XXX TODO Disable proceeding with insecure hash value.
#define BAD_INTEGRITY_HASH "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

#ifndef ___RUNTIME_INTEGRITY_HASH___
#define ___RUNTIME_INTEGRITY_HASH___ BAD_INTEGRITY_HASH
#endif // ___RUNTIME_INTEGRITY_HASH___

//======================================================================

#define	XMHF_SLAB_STACKSIZE		(16384)

//#define XMHF_SLAB_NUMBEROFSLABS			14
#define XMHF_SLAB_NUMBEROFSLABS			2

#define XMHF_SLAB_REGION_SHARED_RODATA 	0x11000000
#define XMHF_SLAB_REGION_START			0x12000000

#define XMHF_SLAB_INITBS_REGION_START	0x13000000
#define XMHF_SLAB_INIT_REGION_START		0x14000000
#define XMHF_SLAB_IHUB_REGION_START		0x15000000
#define XMHF_SLAB_COREAPI_REGION_START	0x16000000

#define XMHF_SLAB_HYPAPP_HYPERDEP_REGION_START	0x18000000

#define XMHF_SLAB_NEXT_REGION_START		0x19000000

#endif //__XMHF_CONFIG_H__
