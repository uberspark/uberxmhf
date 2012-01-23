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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

//types.h - base types
#ifndef __EMHF_TYPES_H_
#define __EMHF_TYPES_H_


//----------------------------------------------------------------------
//EMHF configurable defines
//XXX: to sort

//runtime base address (virtual)
#define __TARGET_BASE	0xC0000000

//"sl" parameter block magic value
#define SL_PARAMETER_BLOCK_MAGIC	0xDEADBEEF

//"runtime" parameter block magic value
#define RUNTIME_PARAMETER_BLOCK_MAGIC	0xF00DDEAD

//16K stack for each core during runtime
#define RUNTIME_STACK_SIZE  (16384)     

//8K stack for each core in "init"
#define INIT_STACK_SIZE	(8192)					

//max. cores/vcpus we support currently
#define MAX_MIDTAB_ENTRIES  (4)
#define MAX_PCPU_ENTRIES  	(MAX_MIDTAB_ENTRIES)
#define MAX_VCPU_ENTRIES    (MAX_PCPU_ENTRIES)


#define MAX_E820_ENTRIES    (64)  //maximum E820 entries we support, 64 should
                                  //be enough


//preferred TPM locality to use for access inside hypervisor
//needs to be 2 or 1 (4 is hw-only, 3 is sinit-only on Intel)
#define EMHF_TPM_LOCALITY_PREF 2


//guest boot record is always loaded at 0000:7C00
#define __GUESTOSBOOTMODULE_BASE		0x7c00
#define __GUESTOSBOOTMODULESUP1_BASE	0x7C00

#define __CS 0x0008 /* Selector for GDT entry 1. RPL 0 */
#define __DS 0x0010 /* Selector for GDT enry 0. RPL 0 */
#define __TRSEL 0x0018  //selector for TSS


//size of runtime IDT, 32 exception vectors each 8 bytes
#define	SIZE_RUNTIME_IDT	(8*32)

#define MPFP_SIGNATURE (0x5F504D5FUL) //"_MP_"
#define MPCONFTABLE_SIGNATURE (0x504D4350UL)  //"PCMP"


#define AP_BOOTSTRAP_CODE_SEG 0x1000
#define SLB_BOOTSTRAP_CODE_BASE 0x40000000 /* 0x80000 */ /* 0x20000 */

#ifdef __NESTED_PAGING__
#define ASID_GUEST_KERNEL 2
#endif

//LAPIC emulation defines
#define LAPIC_OP_RSVD   (3)
#define LAPIC_OP_READ   (2)
#define LAPIC_OP_WRITE  (1)

//VMX runtime TSS size
#define VMX_RUNTIME_TSS_SIZE    (4096)

#define TEMPORARY_HARDCODED_MLE_SIZE       0x10000
#define TEMPORARY_MAX_MLE_HEADER_SIZE      0x80
#define TEMPORARY_HARDCODED_MLE_ENTRYPOINT TEMPORARY_MAX_MLE_HEADER_SIZE


//VMX Unrestricted Guest (UG) E820 hook support
//we currently use the BIOS data area (BDA) unused region
//at 0x0040:0x00AC
#define	VMX_UG_E820HOOK_CS				(0x0040)	
#define	VMX_UG_E820HOOK_IP				(0x00AC)


#define BAD_INTEGRITY_HASH "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"

/* SHA-1 hash of runtime should be defined during build process.
 * However, if it's not, don't fail.  Just proceed with all zeros.
 * XXX TODO Disable proceeding with insecure hash value. */
#ifndef ___RUNTIME_INTEGRITY_HASH___
#define ___RUNTIME_INTEGRITY_HASH___ BAD_INTEGRITY_HASH
#endif /*  ___RUNTIME_INTEGRITY_HASH___ */

//max. size in bytes for runtime options
#define RPB_MAX_RNTMOPTIONS_SIZE		1024		

//----------------------------------------------------------------------



#ifndef __ASSEMBLY__

typedef u32 	paddr_t;		//physical address
typedef void* 	hva_t; 			//hypervisor virtual address 
typedef u64 	spa_t; 			//system physical address 
typedef u32 	gva_t; 			//guest virtual address. we only support 32-bit guests 
typedef u64 	gpa_t; 			//guest physical address. can be 64-bit with PAE 


//"golden" digest values injected using CFLAGS during build process
//NOTE: NO WAY TO SELF-CHECK slbelow64K; JUST A SANITY-CHECK
typedef struct _integrity_measurement_values {
    u8 sha_slbelow64K[20]; // TODO: play nice with SHA_DIGEST_LENGTH in sha1.h
    u8 sha_slabove64K[20];
    u8 sha_runtime[20];
} INTEGRITY_MEASUREMENT_VALUES;


//NOTE: The declaration here _MUST_ match definition of RPB in runtimesup.S	
typedef struct {
	u32 magic;
	u32 XtVmmEntryPoint;
	u32 XtVmmPdptBase;
	u32 XtVmmPdtsBase;
	u32 XtVmmNpdtBase;
	u32 XtVmmNestedNpdtBase;
	u32 XtGuestOSBootModuleBase;
	u32 XtGuestOSBootModuleSize;
	u32 XtGuestOSBootModuleBaseSup1;
	u32 XtGuestOSBootModuleSizeSup1;
	u32 XtVmmStackBase;
	u32 XtVmmStackSize;
	u32 XtVmmGdt;
	u32 XtVmmNetworkAdapterStructureBase;
	u32 XtVmmHsaveBase;
	u32 XtVmmVMCBBase;
	u32 XtVmmIopmBase;
	u32 XtVmmNestedPdptBase;
	u32 XtVmmNestedPdtsBase;
	u32 XtVmmNestedPtsBase;
	u32 XtVmmIdt;
	u32 XtVmmIdtFunctionPointers;
	u32 XtVmmIdtEntries;
	u32 XtVmmE1000DescBase;
	u32 XtVmmE1000HeaderBase;
	u32 XtVmmE1000BodyBase;
	u32 XtVmmRuntimePhysBase;
	u32 XtVmmRuntimeVirtBase;
	u32 XtVmmRuntimeSize;
	u32 XtVmmE820Buffer;
	u32 XtVmmE820NumEntries;
	u32 XtVmmMPCpuinfoBuffer;
	u32 XtVmmMPCpuinfoNumEntries;
	u32 XtVmmTSSBase;
	u32 RtmSVMDevBitmapBase;
	u32 RtmVMXVTdPdpt;
	u32 RtmVMXVTdPdts;
	u32 RtmVMXVTdPts;
	u32 RtmVMXVTdRET;
	u32 RtmVMXVTdCET;
    //uart_config_t uart_config;	        /* runtime options parsed in init and passed forward */
    u8	RtmOptions[RPB_MAX_RNTMOPTIONS_SIZE]; /* runtime options parsed in init and passed forward */
	u32 isEarlyInit;					//1 for an "early init" else 0 (late-init)
} __attribute__((packed)) RPB, *PRPB;


//"sl" parameter block structure 
typedef struct _sl_parameter_block {
	u32 magic;	//magic identifier
	u32 hashSL;	//hash of the secure loader
	u32 errorHandler;	//error handler
	u32 isEarlyInit;	//"early" or "late" init
	u32 numE820Entries;		//number of E820 entries
	//GRUBE820 e820map[MAX_E820_ENTRIES];	//E820 memory-map buffer
	u8  memmapbuffer[1280];			//max. 64 entries of 20 bytes each describing the system memory map
	u32 numCPUEntries;	//number of cores
	//PCPU pcpus[MAX_PCPU_ENTRIES];	//CPU table buffer
	u8  cpuinfobuffer[64];			//max. 4 entries of 16 bytes each describing each physical core in the system
	u32 runtime_size;			//size of the runtime image
	u32 runtime_osbootmodule_base;	//guest OS bootmodule base
	u32 runtime_osbootmodule_size;	//guest OS bootmodule size
    // Performance measurements related to DRTM
    u64 rdtsc_before_drtm;
    u64 rdtsc_after_drtm;

    /* runtime options parsed in init and passed forward */
    //uart_config_t uart_config;
    u8	options[RPB_MAX_RNTMOPTIONS_SIZE]; /* runtime options parsed in init and passed forward */
} __attribute__((packed)) SL_PARAMETER_BLOCK;





#endif /*ifndef __ASSEMBLY__*/

#endif /* __EMHF_TYPES_H_ */
