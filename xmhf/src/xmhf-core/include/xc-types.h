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

// XMHF core specific data types
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XC_TYPES_H__
#define __XC_TYPES_H__


#ifndef __ASSEMBLY__

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


typedef struct {
		u32 cpuid;				//unique CPU id
		bool is_bsp;			//true if CPU is the boot-strap processor
		bool is_quiesced;		//true if CPU is quiesced
		u32 index_cpuarchdata;	//index into CPU arch. specific data buffer
		u32 index_partitiondata;	//index into partition data buffer
} xc_cpu_t;

typedef struct {
		u32 cpuid;				//unique CPU id
		u32 index_cpudata;		//index into CPU data buffer
} xc_cputable_t;

typedef struct {
		u32 partitionid;			//unique partition id
		u32 partitiontype;			//primary or secondary
		u32 index_hwpagetabledata;	//index into h/w page table data buffer
		u32 indices_cpudata[MAX_PLATFORM_CPUS];	//indices into cpu data buffer for all cpus allocated to the partition
		u32 number_of_cpus;			//number of cpus allocated to the partition
} xc_partition_t;

//variables
//XXX: move them into relevant component headers

// platform cpus
extern xc_cpu_t g_xc_cpu[MAX_PLATFORM_CPUS] __attribute__(( section(".data") ));

// partitions
extern xc_partition_t g_xc_partition[MAX_PARTITIONS] __attribute__(( section(".data") ));

// cpu table
extern xc_cputable_t g_xc_cputable[MAX_PLATFORM_CPUS] __attribute__(( section(".data") ));

  
#endif //__ASSEMBLY__

#endif //__XC_TYPES_H__
