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

// XMHF core global data declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XC_GLOBALDATA_H__
#define __XC_GLOBALDATA_H__


#ifndef __ASSEMBLY__

// this is in xc.lds
extern u8 paramcore_start[];
extern u8 paramhypapp_start[];


// XMHF boot information block
extern XMHF_BOOTINFO *xcbootinfo;

//core DMA protection buffer (if DMA protections need to be re-initialized on the target platform)
extern u8 g_core_dmaprot_buffer[SIZE_CORE_DMAPROT_BUFFER] __attribute__(( section(".palign_data") ));

//core parameter block
extern XMHF_HYPAPP_PARAMETERBLOCK *paramcore;

//hypapp parameter block
extern XMHF_HYPAPP_PARAMETERBLOCK *paramhypapp;

//hypapp header
extern XMHF_HYPAPP_HEADER *g_hypappheader;

//hypapp callback hub entry point and hypapp top of stack
extern u32 hypapp_cbhub_pc;
extern u32 hypapp_tos;

// platform cpus
extern xc_cpu_t g_xc_cpu[MAX_PLATFORM_CPUS] __attribute__(( section(".data") ));

// count of platform cpus
extern u32 g_xc_cpu_count __attribute__(( section(".data") ));

// platform cpu arch. data buffer
//u8 g_xc_cpuarchdata[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUARCHDATA_SIZE] __attribute__(( section(".palign_data") ));
extern xc_cpuarchdata_t g_xc_cpuarchdata[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUARCHDATA_SIZE] __attribute__(( section(".data"), aligned(4096) ));

// platform cpu stacks
//extern u8 g_xc_cpustack[MAX_PLATFORM_CPUS][MAX_PLATFORM_CPUSTACK_SIZE] __attribute__(( section(".stack") ));

// primary partitions
extern xc_partition_t g_xc_primary_partition[MAX_PRIMARY_PARTITIONS] __attribute__(( section(".data") ));

// secondary partitions
extern xc_partition_t g_xc_secondary_partition[MAX_SECONDARY_PARTITIONS] __attribute__(( section(".data") ));

// primary partition hpt data buffers
extern xc_partition_hptdata_t g_xc_primary_partition_hptdata[MAX_PRIMARY_PARTITIONS][MAX_PRIMARY_PARTITION_HPTDATA_SIZE] __attribute__(( section(".data"), aligned(4096) ));

// secondary partition hpt data buffers
extern xc_partition_hptdata_t g_xc_secondary_partition_hptdata[MAX_SECONDARY_PARTITIONS][MAX_SECONDARY_PARTITION_HPTDATA_SIZE] __attribute__(( section(".data"), aligned(4096) ));

// primary partition trap mask data buffers
extern xc_partition_trapmaskdata_t g_xc_primary_partition_trapmaskdata[MAX_PRIMARY_PARTITIONS][MAX_PRIMARY_PARTITION_TRAPMASKDATA_SIZE] __attribute__(( section(".data"), aligned(4096) ));

// partition data structure pointer for the richguest
extern xc_partition_t *xc_partition_richguest;

// cpu table
extern xc_cputable_t g_xc_cputable[MAX_PLATFORM_CPUS] __attribute__(( section(".data") ));

  
#endif //__ASSEMBLY__


#endif //__XC_GLOBALDATA_H__
