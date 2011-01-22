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

#ifndef __ASSEMBLY__

//PCI type-1 access address format
typedef union pci_config_reg_addr 
{
  u32 bytes;
  struct{
    u32 offset:8; 			//bits 0-7 index in device config space 
    u32 function:3; 		//bits 8-10 function  
    u32 device:5; 			//bits 11-15 device 
    u32 bus:8; 					//bits 16-23 bus 
    u32 offset_high:4;	//bits 24-27 high 4-bits of index for PCIe
    u32 resv:3;					//bits 28-30 reserved
    u32 enabled:1; 			//bit 31 address should be sent to config space 
  }fields;
}  __attribute__ ((packed)) pci_config_reg_addr_t;

//macro to encode a device and function into a 8-bit value
#define PCI_DEVFN(device, function) ((((device) & 0x1f) << 3) | ((function) & 0x07))

//macro to encode a bus, device, function and index into a 32-bit
//PCI type-1 address
#define PCI_TYPE1_ADDRESS(bus, device, function, index) \
        (0x80000000 | ((index & 0xF00) << 16) | (bus << 16) \
        | (PCI_DEVFN(device, function) << 8) | (index & 0xFC))

//does a PCI type-1 read of PCI config space for a given bus, device, 
//function and index
//len = 1(byte), 2(word) and 4(dword)
//value is a pointer to a 32-bit dword which contains the value read
void pci_type1_read(u32 bus, u32 device, u32 function, u32 index, u32 len,
			u32 *value);
			
//does a PCI type-1 write of PCI config space for a given bus, device, 
//function and index
//len = 1(byte), 2(word) and 4(dword)
//value contains the value to be written
void pci_type1_write(u32 bus, u32 device, u32 function, u32 index, u32 len,
	u32 value);

//PCI subsystem initialization
//check that PCI chipset supports type-1 accesses
//true for most systems after 2001
void pci_initialize(void);
			


#endif /* __ASSEMBLY__ */
#endif /* __PCI_H__ */
