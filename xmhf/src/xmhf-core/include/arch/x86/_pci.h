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

//pci.h - peripheral component interconnect (PCI) spec.
// implementation declarations
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __PCI_H__
#define __PCI_H__

//PCI type-1 access ports
#define PCI_CONFIG_ADDR_PORT 	(0x0cf8)
#define PCI_CONFIG_DATA_PORT 	(0x0cfc)

//PCI configuration header indices (as per PCI local bus spec. v3.0)
#define PCI_CONF_HDR_IDX_VENDOR_ID 							0x0
#define PCI_CONF_HDR_IDX_DEVICE_ID							0x02
#define PCI_CONF_HDR_IDX_COMMAND          			0x04
#define PCI_CONF_HDR_IDX_STATUS	          			0x06
#define PCI_CONF_HDR_IDX_REVISION_ID						0x08
#define PCI_CONF_HDR_IDX_CLASS_CODE							0x09
#define	PCI_CONF_HDR_IDX_HEADER_TYPE						0x0E
#define PCI_CONF_HDR_IDX_CAPABILITIES_POINTER		0x34

//PCI "command" register
#define PCI_COMMAND_IO          	0x1     /* Enable response in I/O space */
#define PCI_COMMAND_MEMORY      	0x2     /* Enable response in Memory space */
#define PCI_COMMAND_MASTER      	0x4     /* Enable bus mastering */
#define PCI_COMMAND_SPECIAL     	0x8     /* Enable response to special cycles */
#define PCI_COMMAND_INVALIDATE  	0x10    /* Use memory write and invalidate */
#define PCI_COMMAND_VGA_PALETTE 	0x20   	/* Enable palette snooping */
#define PCI_COMMAND_PARITY      	0x40    /* Enable parity checking */
#define PCI_COMMAND_WAIT        	0x80    /* Enable address/data stepping */
#define PCI_COMMAND_SERR        	0x100   /* Enable SERR */
#define PCI_COMMAND_FAST_BACK   	0x200   /* Enable back-to-back writes */
#define PCI_COMMAND_INTX_DISABLE 	0x400 	/* INTx Emulation Disable */

//maximum PCI bus, device and function numbers
#define PCI_BUS_MAX					256
#define PCI_DEVICE_MAX			32
#define	PCI_FUNCTION_MAX		8	

//AMD PCI configuration space constants
#define	PCI_VENDOR_ID_AMD										0x1022	//Vendor ID for AMD

#define	PCI_DEVICE_ID_AMD_HT_CONFIGURATION	0x1200	//Device ID for AMD Hypertransport Configuration 
#define	PCI_DEVICE_ID_AMD_ADDRESSMAP				0x1201	//Device ID for AMD Address Map
#define PCI_DEVICE_ID_AMD_DRAMCONTROL				0x1202	//Device ID for AMD DRAM Controller
#define PCI_DEVICE_ID_AMD_MISCCONTROL				0x1203	//Device ID for AMD Miscellaneous Control
#define PCI_DEVICE_ID_AMD_LINKCONTROL				0x1204	//Device ID for AMD Link Control

#define PCI_CAPABILITIES_POINTER_ID_DEV			0x0F	//PCI capability ID for SVM DEV


#ifndef __ASSEMBLY__

//macro to encode a device and function into a 8-bit value
#define PCI_DEVICE_FN(device, function) ((((device) & 0x1f) << 3) | ((function) & 0x07))

//macro to encode a bus, device, function and index into a 32-bit
//PCI type-1 address
#define PCI_TYPE1_ADDRESS(bus, device, function, index) \
        (0x80000000 | ((index & 0xF00) << 16) | (bus << 16) \
        | (PCI_DEVICE_FN(device, function) << 8) | (index & 0xFC))



#endif /* __ASSEMBLY__ */
#endif /* __PCI_H__ */
