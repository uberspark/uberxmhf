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

/**
 * rntm-data.c
 * EMHF runtime data definitions
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <emhf.h> 

//runtime parameter block pointer 
RPB *rpb __attribute__(( section(".data") )); 

//runtime DMA protection buffer
u8 g_rntm_dmaprot_buffer[(PAGE_SIZE_4K + (PAGE_SIZE_4K * PAE_PTRS_PER_PDPT) 
					+ (PAGE_SIZE_4K * PAE_PTRS_PER_PDPT * PAE_PTRS_PER_PDT) + PAGE_SIZE_4K +
					(PAGE_SIZE_4K * PCI_BUS_MAX))] __attribute__(( section(".palign_data") ));

//variable that is incremented by 1 by all cores that cycle through appmain
//successfully, this should be finally equal to g_midtable_numentries at
//runtime which signifies that EMHF appmain executed successfully on all
//cores
u32 g_appmain_success_counter __attribute__(( section(".data") )) = 0;

//SMP lock for the above variable
u32 g_lock_appmain_success_counter __attribute__(( section(".data") )) = 1;
