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


typedef uint32_t 	paddr_t;		//physical address
typedef void* 	hva_t; 			//hypervisor virtual address
typedef uint64_t 	spa_t; 			//system physical address
typedef uint32_t 	gva_t; 			//guest virtual address. we only support 32-bit guests
typedef uint64_t 	gpa_t; 			//guest physical address. can be 64-bit with PAE
typedef void*   dma_addr_t;

//"golden" digest values injected during build process
//NOTE: NO WAY TO SELF-CHECK slbelow64K; JUST A SANITY-CHECK
typedef struct _integrity_measurement_values {
    uint8_t sha_slbelow64K[20]; // TODO: play nice with SHA_DIGEST_LENGTH in sha1.h
    uint8_t sha_slabove64K[20];
    uint8_t sha_runtime[20];
} INTEGRITY_MEASUREMENT_VALUES;

//XXX: this is currently close to GRUB, but is essentially a generic memory map structure
typedef struct _grube820 {
  uint32_t baseaddr_low;
  uint32_t baseaddr_high;
  uint32_t length_low;
  uint32_t length_high;
  uint32_t type;
} __attribute__((packed)) GRUBE820;

#define SIZE_STRUCT_GRUBE820  (sizeof(struct _grube820))

//XXX: this is currently close to x86 platforms, but is essentially a generic physical CPU structure
typedef struct _pcpu {
  uint32_t lapic_id;
  uint32_t lapic_ver;
  uint32_t lapic_base;
  uint32_t isbsp;
} __attribute__((packed)) PCPU;

#define SIZE_STRUCT_PCPU  (sizeof(struct _pcpu))

//----------------------------------------------------------------------
//the master-id table, which is used by the AP bootstrap code
//to locate its own vcpu structure
typedef struct _midtab {
  uint32_t cpu_lapic_id;       //CPU LAPIC id (unique)
  uint32_t vcpu_vaddr_ptr;     //virt. addr. pointer to vcpu struct for this CPU
} __attribute__((packed)) MIDTAB;

#define SIZE_STRUCT_MIDTAB  (sizeof(struct _midtab))

//XMHF_BOOTINFO
typedef struct {
	uint32_t magic;
	uint32_t richguest_bootmodule_base;
	uint32_t richguest_bootmodule_size;
	uint32_t memmapinfo_numentries;
	GRUBE820 memmapinfo_buffer[MAX_E820_ENTRIES];
	uint32_t cpuinfo_numentries;
	PCPU cpuinfo_buffer[MAX_PCPU_ENTRIES];
	uint8_t debugcontrol_buffer[16];
	uint8_t cmdline_buffer[MAX_CMDLINE_BUFFER_SIZE];
	uint8_t filler[2652];
} __attribute__((packed)) XMHF_BOOTINFO;

__attribute__(( section(".sharedro_xcbootinfoptr") )) extern XMHF_BOOTINFO *xcbootinfo;

typedef struct {
		uint32_t cpuid;				//unique CPU id
		uint32_t cpu_index;			//0 based index
} __attribute__((packed)) xmhf_cputable_t;


//-------------------------------------------------------

//XMHF core api CPU descriptor type
typedef struct {
	bool isbsp;
	uint32_t cpu_index;
} cpu_desc_t;

//XMHF core api partition descriptor type
typedef struct {
	uint32_t partition_index;
	uint32_t numcpus;
} partition_desc_t;

//XMHF core api context descriptor type (context = partition + cpu pair)
typedef struct {
	partition_desc_t partition_desc;
	cpu_desc_t cpu_desc;
} context_desc_t;


#endif /*ifndef __ASSEMBLY__*/

#endif /* __XMHF_TYPES_H_ */
