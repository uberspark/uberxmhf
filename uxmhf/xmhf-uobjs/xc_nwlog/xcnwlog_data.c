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

#include <xmhf.h>
#include <xmhfgeec.h>
#include <xmhf-debug.h>

#include <xc.h>
#include <xc_nwlog.h>

//__attribute__((section(".slab_dmadata"))) xcnwlog_ls_element_t xcnwlog_lsdma[XC_NWLOG_BUF_MAXIDX][XC_NWLOG_BUF_MAXELEM];

__attribute__((section(".slab_dmadata"))) __attribute__((aligned(4096))) uint8_t xcnwlog_desc[PAGE_SIZE_4K];

__attribute__((section(".slab_dmadata"))) __attribute__((aligned(4096))) xcnwlog_packet_t xcnwlog_packet;

__attribute__((section(".data"))) xcnwlog_ls_element_t xcnwlog_ls[XC_NWLOG_BUF_MAXIDX][XC_NWLOG_BUF_MAXELEM];
__attribute__((section(".data"))) uint32_t xcnwlog_ls_index[XC_NWLOG_BUF_MAXIDX]= { 0 };


__attribute__((section(".data"))) char e1000_driver_name[] = "e1000";
__attribute__((section(".data"))) char e1000_driver_string[] = "Intel(R) PRO/1000 Network Driver";
__attribute__((section(".data"))) char e1000_driver_version[] = "based on 7.3.20-k2";


__attribute__((section(".data"))) pci_device_t e1000_dev;
__attribute__((section(".data"))) struct e1000_adapter e1000_adapt;
__attribute__((section(".data"))) unsigned int e1000_irq = 18;

//------------------------------------------------------------------------------
//[CONFIGURATION:START]
//this changes according to deployment platform
__attribute__((section(".data"))) unsigned char e1000_dst_macaddr[] = "";
__attribute__((section(".data"))) unsigned char e1000_pkt_type[] = {0x80, 0x86};
//[CONFIGURATION:END]
//------------------------------------------------------------------------------





