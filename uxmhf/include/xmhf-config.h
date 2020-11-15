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


//total unverified hypervisor slabs
#define XMHFGEEC_TOTAL_UHSLABS __XMHFGEEC_TOTAL_UHSLABS__

//total unverified guest slabs
#define XMHFGEEC_TOTAL_UGSLABS __XMHFGEEC_TOTAL_UGSLABS__



//max. include device list entries
//#define XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES __XMHF_CONFIG_MAX_INCLDEVLIST_ENTRIES__

//max. exclude device list entries
//#define XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES __XMHF_CONFIG_MAX_EXCLDEVLIST_ENTRIES__


//max. memoffset entries
//#define XMHF_CONFIG_MAX_MEMOFFSET_ENTRIES __XMHF_CONFIG_MAX_MEMOFFSET_ENTRIES__



//"runtime" parameter block magic value
#define RUNTIME_PARAMETER_BLOCK_MAGIC	0xF00DDEAD

#define SL_PARAMETER_BLOCK_MAGIC	0xF00DDEAD

//16K stack for each core during runtime
#define RUNTIME_STACK_SIZE  		(16384)

//8K stack for each core in "init"
#define INIT_STACK_SIZE			(8192)

//max. size of command line parameter buffer
#define MAX_CMDLINE_BUFFER_SIZE		(128)

//max. cores/vcpus we support currently
//#ifndef __XMHF_VERIFICATION__
//	#define	MAX_PLATFORM_CPUS	(256)
//#else
//	#define	MAX_PLATFORM_CPUS	(1)
//#endif

//max. platform devices we support currently
#define MAX_PLATFORM_DEVICES            (64)

#define MAX_MIDTAB_ENTRIES  		(MAX_PLATFORM_CPUS)
#define MAX_PCPU_ENTRIES  		(MAX_PLATFORM_CPUS)
#define MAX_VCPU_ENTRIES    		(MAX_PLATFORM_CPUS)

//max. primary partitions we support
#define	MAX_PRIMARY_PARTITIONS		(1)

//max. secondary partitions we support
#define	MAX_SECONDARY_PARTITIONS	(4)

//max. size of primary partition HPT data buffer
#define	MAX_PRIMARY_PARTITION_HPTDATA_SIZE	(2054*4096)

//max. size of primary partition HPT data buffer
#define	MAX_SECONDARY_PARTITION_HPTDATA_SIZE	(6*4096)

//max. partition trapmask data buffer
#define MAX_PRIMARY_PARTITION_TRAPMASKDATA_SIZE	(4*4096)

//max. size of CPU arch. specific data (32K default)
#define	MAX_PLATFORM_CPUARCHDATA_SIZE		(8*4096)

//max. size of CPU stack (16K default)
#define MAX_PLATFORM_CPUSTACK_SIZE		(4*4096)

//max. number of arch. specific parameters for hypapp callback
#define MAX_XC_HYPAPP_CB_ARCH_PARAMS	8

//maximum system memory map entries (e.g., E820) currently supported
#define MAX_E820_ENTRIES    		(64)

// SHA-1 hash of runtime should be defined during build process.
// However, if it's not, don't fail.  Just proceed with all zeros.
// XXX TODO Disable proceeding with insecure hash value.
#define BAD_INTEGRITY_HASH "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

#ifndef ___RUNTIME_INTEGRITY_HASH___
#define ___RUNTIME_INTEGRITY_HASH___ BAD_INTEGRITY_HASH
#endif // ___RUNTIME_INTEGRITY_HASH___

//======================================================================

//#define	XMHF_SLAB_STACKSIZE		(16384)




//////
// TODO: automatically generate the constants below based on build conf.
// for now, manually keep in sync based on the conf. selected
//////

//#define XMHFGEEC_MAX_SLABS                  32
//#define XMHFGEEC_TOTAL_SLABS                16

#define XMHFGEEC_SLAB_GEEC_SENTINEL         0
#define XMHFGEEC_SLAB_GEEC_PRIME            1
#define XMHFGEEC_SLAB_XC_INIT               2
#define XMHFGEEC_SLAB_XC_EXHUB              3
#define XMHFGEEC_SLAB_XC_IHUB               4
#define XMHFGEEC_SLAB_XC_NWLOG              5
#define XMHFGEEC_SLAB_UAPI_GCPUSTATE        6
#define XMHFGEEC_SLAB_UAPI_HCPUSTATE        7
#define XMHFGEEC_SLAB_UAPI_SLABMEMPGTBL     8
#define XMHFGEEC_SLAB_UAPI_SYSDATA	    9
#define UOBJ_UAPI_IOTBL			    10
#define UOBJ_UAPI_UHMPGTBL		    11
#define XMHFGEEC_SLAB_XH_SYSCALLLOG         12
#define XMHFGEEC_SLAB_XH_UHCALLTEST         13
//#define XMHFGEEC_SLAB_XH_HYPERDEP	         13
#define XMHFGEEC_SLAB_XH_SSTEPTRACE         14
#define XMHFGEEC_SLAB_XG_RICHGUEST          15




#define XMHFGEEC_VHSLAB_BASE_IDX	    0
#define XMHFGEEC_VHSLAB_MAX_IDX		    13
#define XMHFGEEC_UHSLAB_BASE_IDX	    14
#define XMHFGEEC_UHSLAB_MAX_IDX		    14
#define XMHFGEEC_UGSLAB_BASE_IDX	    15
#define XMHFGEEC_UGSLAB_MAX_IDX		    15


#define XMHFGEEC_TOTAL_VHSLABS		((XMHFGEEC_VHSLAB_MAX_IDX - XMHFGEEC_VHSLAB_BASE_IDX) + 1)
#define __XMHFGEEC_TOTAL_UHSLABS	((XMHFGEEC_UHSLAB_MAX_IDX - XMHFGEEC_UHSLAB_BASE_IDX) + 1)
#define __XMHFGEEC_TOTAL_UGSLABS	((XMHFGEEC_UGSLAB_MAX_IDX - XMHFGEEC_UGSLAB_BASE_IDX) + 1)


#if (XMHFGEEC_TOTAL_UHSLABS != __XMHFGEEC_TOTAL_UHSLABS)
	#error FATAL: Mistmatch in XMHFGEEC_TOTAL_UHSLABS (common.mk.in) and __XMHFGEEC_TOTAL_UHSLABS (xmhf-config.h)
#endif

#if (XMHFGEEC_TOTAL_UGSLABS != __XMHFGEEC_TOTAL_UGSLABS)
	#error FATAL: Mistmatch in XMHFGEEC_TOTAL_UGSLABS (common.mk.in) and __XMHFGEEC_TOTAL_UGSLABS (xmhf-config.h)
#endif

//////




//======================================================================
//XMHF platform/arch. specific configurable constant definitions

//----------------------------------------------------------------------
// XMHF platform memory map
	//physical memory extents of the XMHF framework
	#define __TARGET_BASE_XMHF		__XMHF_CONFIG_LOADADDR__
	#define __TARGET_SIZE_XMHF		__XMHF_CONFIG_LOADMAXSIZE__
	#define __TARGET_MAX_XMHF		__XMHF_CONFIG_LOADMAXADDR__
	#define __TARGET_MAX_SYS		__XMHF_CONFIG_MAXSYSADDR__


	//physical address where the XMHF boot-loader is loaded (e.g., via GRUB)
	#define __TARGET_BASE_BOOTLOADER		0x01E00000		//30MB

	//size of the boot-loader should put the bootloader base + size to
	//match __TARGET_BASE_XMHF
	#define __TARGET_SIZE_BOOTLOADER		(__TARGET_BASE_XMHF - __TARGET_BASE_BOOTLOADER)

	//physical address of geec_prime slab (acts as secure loader)
	#define __TARGET_BASE_SL			(__TARGET_BASE_XMHF + 0x01200000)

	#define __TARGET_SIZE_SL			0x00200000

//----------------------------------------------------------------------

//"sl" parameter block magic value
//#define SL_PARAMETER_BLOCK_MAGIC		0xDEADBEEF

//size of core DMA protection buffer (if platform DMA protections need to be re-initialized within the core)
#define SIZE_CORE_DMAPROT_BUFFER		(128*1024)

//preferred TPM locality to use for access inside hypervisor
//needs to be 2 or 1 (4 is hw-only, 3 is sinit-only on Intel)
#define EMHF_TPM_LOCALITY_PREF 2

//where the guest OS boot record is loaded
#define __GUESTOSBOOTMODULE_BASE		0x7c00
#define __GUESTOSBOOTMODULESUP1_BASE	        0x7C00

//----------------------------------------------------------------------

//code segment of memory address where APs startup initially
//address 0x1000:0x0000 or 0x10000 physical
#define X86SMP_APBOOTSTRAP_CODESEG 		0x1000

//data segment of memory address where APs startup initially
//address 0x1100:0x0000 or 0x11000 physical
#define X86SMP_APBOOTSTRAP_DATASEG 		0x1100

#define X86SMP_APBOOTSTRAP_MAXGDTENTRIES    4

#define X86SMP_LAPIC_MEMORYADDRESS          0xFEE00000
#define X86SMP_LAPIC_ID_MEMORYADDRESS       0xFEE00020

#define TPM_LOCALITY_BASE                   0xfed40000

//----------------------------------------------------------------------

//TXT SENTER MLE specific constants
#define TEMPORARY_HARDCODED_MLE_SIZE       0x10000
#define TEMPORARY_MAX_MLE_HEADER_SIZE      0x80
#define TEMPORARY_HARDCODED_MLE_ENTRYPOINT TEMPORARY_MAX_MLE_HEADER_SIZE

//VMX Unrestricted Guest (UG) E820 hook support
//we currently use the BIOS data area (BDA) unused region
//at 0x0040:0x00AC
#define	VMX_UG_E820HOOK_CS			(0x0040)
#define	VMX_UG_E820HOOK_IP			(0x00AC)


#define     MAX_X86_APIC_ID     256


#define     MAX_SLAB_DMADATA_SIZE           (32*1024*1024)
#define     MAX_SLAB_DMADATA_PDT_ENTRIES    (MAX_SLAB_DMADATA_SIZE/(2*1024*1024))


// segment selectors
#define         __NULLSEL           0x0000      //NULL selector
#define 	__CS_CPL0 	    0x0008 	//CPL-0 code segment selector
#define 	__DS_CPL0 	    0x0010 	//CPL-0 data segment selector
#define		__CS_CPL3	    0x001b	//CPL-3 code segment selector
#define		__DS_CPL3	    0x0023      //CPL-3 data segment selector
#define		__CS_CPL3_SE        0x002b	//CPL-3 code segment selector
#define		__DS_CPL3_SE	    0x0033      //CPL-3 data segment selector
#define 	__TRSEL 	    0x0038      //TSS (task) selector

// max. segment descriptors not including TSS descriptors
#define     XMHFGEEC_MAX_GDT_CODEDATA_DESCRIPTORS   7

#define	EMHF_XCPHANDLER_MAXEXCEPTIONS	32



#ifndef __ASSEMBLY__

/*#if defined (__DEBUG_SERIAL__)

extern uint8_t _libxmhfdebugdata_start[];
extern uint8_t _libxmhfdebugdata_end[];

#define     ADDR_LIBXMHFDEBUGDATA_START           ((uint32_t)_libxmhfdebugdata_start)
#define     ADDR_LIBXMHFDEBUGDATA_END             ((uint32_t)_libxmhfdebugdata_end)

#endif // defined
*/

#endif // __ASSEMBLY__


#endif //__XMHF_CONFIG_H__
