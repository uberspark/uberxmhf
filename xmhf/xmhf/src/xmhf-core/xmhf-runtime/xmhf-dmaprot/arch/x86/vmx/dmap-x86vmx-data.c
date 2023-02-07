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

/**
 * dmap-x86vmx-data.c
 * EMHF DMA protection component implementation for x86 VMX
 * data definitions
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h> 

//VMX VT-d page table buffers; we support a 3 level page-table walk, 
//4kb pdpt, 4kb pdt and 4kb pt and each entry in pdpt, pdt and pt is 64-bits
u8 g_vmx_vtd_pdp_table[PAGE_SIZE_4K] __attribute__(( section(".palign_data") )); 
u8 g_vmx_vtd_pd_tables[PAGE_SIZE_4K * PAE_PTRS_PER_PDPT] __attribute__(( section(".palign_data") ));
u8 g_vmx_vtd_p_tables[PAGE_SIZE_4K * PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT] __attribute__(( section(".palign_data") ));

//VMX VT-d Root Entry Table (RET)
//the RET is 4kb, each root entry (RE) is 128-bits
//this gives us 256 entries in the RET, each corresponding to a PCI bus num. (0-255)
u8 g_vmx_vtd_ret[PAGE_SIZE_4K] __attribute__(( section(".palign_data") )); 

//VMX VT-d Context Entry Table (CET)
//each RE points to a context entry table (CET) of 4kb, each context entry (CE)
//is 128-bits which gives us 256 entries in the CET, accounting for 32 devices
//with 8 functions each as per the PCI spec.
u8 g_vmx_vtd_cet[PAGE_SIZE_4K * PCI_BUS_MAX] __attribute__(( section(".palign_data") ));
