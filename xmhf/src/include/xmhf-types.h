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

//types.h - base types
#ifndef __XMHF_TYPES_H_
#define __XMHF_TYPES_H_


#ifndef __ASSEMBLY__

//define a pseudo attribute definition that allows us to annotate 
//core API/hypapp callbacks function parameters
//core-ro = parameter in core and is read-only within hypapp
//hypapp-ro = parameter in hypapp area is read-only in core
//core-rw = parameter in core and is read-write within core
//hypapp-rw = parameter in hypapp area and is rad-write in hypapp
#define __xmhfattribute__(x)

//define XMHF core API aggregate return type
//allows us to return multiple values without using pointers to pointers
typedef struct xmhfcoreapiretval {
	u64 returnval;
	void *returnptr1;
} xmhfcoreapiretval_t;

//XMHF CPU descriptor type
typedef struct {
	uint32_t id;
	bool isbsp;
} cpu_desc_t;
	
//XMHF partition descriptor type
typedef struct {
	uint32_t id;
} partition_desc_t;

//XMHF context descriptor type (context = partition + cpu pair)
typedef struct {
	partition_desc_t partition_desc;
	cpu_desc_t cpu_desc;
} context_desc_t;

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

//XXX: this is currently close to GRUB, but is essentially a generic memory map structure
typedef struct _grube820 {
  u32 baseaddr_low;
  u32 baseaddr_high;
  u32 length_low;
  u32 length_high;
  u32 type;  
} __attribute__((packed)) GRUBE820;

#define SIZE_STRUCT_GRUBE820  (sizeof(struct _grube820))

//XXX: this is currently close to x86 platforms, but is essentially a generic physical CPU structure
typedef struct _pcpu {
  u32 lapic_id;
  u32 lapic_ver;
  u32 lapic_base;
  u32 isbsp;
} __attribute__((packed)) PCPU;

#define SIZE_STRUCT_PCPU  (sizeof(struct _pcpu))

//----------------------------------------------------------------------
//the master-id table, which is used by the AP bootstrap code
//to locate its own vcpu structure
typedef struct _midtab {
  u32 cpu_lapic_id;       //CPU LAPIC id (unique)
  u32 vcpu_vaddr_ptr;     //virt. addr. pointer to vcpu struct for this CPU
} __attribute__((packed)) MIDTAB;

#define SIZE_STRUCT_MIDTAB  (sizeof(struct _midtab))

//XMHF_BOOTINFO
typedef struct {
	u32 magic;
	u32 physmem_base;
	u32 virtmem_base;
	u32 size;
	u32 entrypoint;
	u32 stack_base;
	u32 stack_size;
	u32 richguest_bootmodule_base;
	u32 richguest_bootmodule_size;
	u32 memmapinfo_numentries;
	u8 memmapinfo_buffer[1280]; //64 entries each of 20 bytes
	u32 cpuinfo_numentries;
	u8 cpuinfo_buffer[128]; //8 entries each of 16 bytes
	u8 debugcontrol_buffer[16];
	u8 cmdline_buffer[128];
} __attribute__((packed)) XMHF_BOOTINFO;

//forward declaration of core boot info structure
extern XMHF_BOOTINFO *xcbootinfo;

/*//"runtime" parameter block structure; arch_rpb (in startup component) 
//is the default definition
typedef struct {
	u32 magic;
	u32 XtVmmEntryPoint;
	u32 XtGuestOSBootModuleBase;
	u32 XtGuestOSBootModuleSize;
	u32 runtime_appmodule_base;
	u32 runtime_appmodule_size;
	u32 XtVmmStackBase;
	u32 XtVmmStackSize;
	u32 XtVmmRuntimePhysBase;
	u32 XtVmmRuntimeVirtBase;
	u32 XtVmmRuntimeSize;
	u32 XtVmmE820Buffer;
	u32 XtVmmE820NumEntries;
	u32 XtVmmMPCpuinfoBuffer;
	u32 XtVmmMPCpuinfoNumEntries;
    u8 RtmUartConfig[16];	        // runtime options parsed in init and passed forward 
    char cmdline[128]; 				// runtime options parsed in init and passed forward 
	u32 isEarlyInit;					//1 for an "early init" else 0 (late-init)
} __attribute__((packed)) RPB, *PRPB;

//forward declaration of runtime parameter block
extern RPB *rpb;	
*/
/*
//"sl" parameter block structure 
typedef struct _sl_parameter_block {
	u32 magic;						//magic identifier
	u32 errorHandler;				//error handler (currently unused)
	u32 isEarlyInit;				//"early" or "late" init
	u32 numE820Entries;				//number of E820 entries
	u8  memmapbuffer[1280];			//max. 64 entries of 20 bytes each describing the system memory map
	u32 numCPUEntries;				//number of cores
	u8  cpuinfobuffer[128];			//max. 8 entries of 16 bytes each describing each physical core in the system
	u32 runtime_size;				//size of the runtime image
	u32 runtime_osbootmodule_base;	//guest OS bootmodule base
	u32 runtime_osbootmodule_size;	//guest OS bootmodule size
	u32 runtime_appmodule_base;		//XMHF hypapp optional module base
	u32 runtime_appmodule_size;		//XMHF hypapp optional module size
    u64 rdtsc_before_drtm;			// Performance measurements related to DRTM
    u64 rdtsc_after_drtm;

    // runtime options parsed in init and passed forward 
    u8 uart_config[16];
    char cmdline[128]; // runtime options parsed in init and passed forward 
} __attribute__((packed)) SL_PARAMETER_BLOCK;
*/

//"sl" parameter block magic value
#define SL_PARAMETER_BLOCK_MAGIC		0xDEADBEEF

//"runtime" parameter block magic value
#define RUNTIME_PARAMETER_BLOCK_MAGIC	0xF00DDEAD




#endif /*ifndef __ASSEMBLY__*/

#endif /* __XMHF_TYPES_H_ */
