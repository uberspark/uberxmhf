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

/* pci.h definitions and functions to read and write PCI configuration space
 * Written for TrustVisor by Arvind Seshadri
 */

#ifndef __PCI_H__
#define __PCI_H__
/* PCI config space ports */
#define CONFIG_ADDR_PORT (u16)0x0cf8
#define CONFIG_DATA_PORT (u16)0x0cfc

#define PCI_CONF_HDR_ID 0x0
#define PCI_CONF_HDR_CMD 0x4
#define PCI_CONF_HDR_CAP 0x34

#define PCI_CAP_OFFSET 0x1

#ifndef __ASSEMBLY__

/* PCI config register address */
typedef union pci_config_reg_addr 
{
  u32 bytes;
  struct{
    u32 offset:8; /* bits 0-7 offset of register in device config space */
    u32 function:3; /* bits 8-10 function number */
    u32 device:5; /* bits 11-15 device number */ 
    u32 bus:8; /* bits 16-23 bus number device is on */
    u32 resv:7; /* bits 24-30 reserved */
    u32 enabled:1; /* bit 31 address should be sent to config space */
  }fields;
}  __attribute__ ((packed)) pci_config_reg_addr_t;

static inline u32 read_pci_config_dword(pci_config_reg_addr_t *ptr)
{
  u32 data;
  
  /* zero out the last two bits, in case we are sent a malformed address */
  ptr->bytes &= 0xfffffffc;

  /* write address to CONFIG_ADDR_PORT */
  outl(ptr->bytes, CONFIG_ADDR_PORT);
  
  /* read data from CONFIG_DATA_PORT */
  data = inl(CONFIG_DATA_PORT);
  
  return data;
}

/* This function is replicated one for read_pci_config_dword, just for 
 * initialization to make sure it is in the init area 
 */
static inline u32 init_read_pci_config_dword(pci_config_reg_addr_t *ptr)  
	__attribute__ ((section ("_init_text")));

static inline u32 init_read_pci_config_dword(pci_config_reg_addr_t *ptr)
{
  u32 data;
  
  /* zero out the last two bits, in case we are sent a malformed address */
  ptr->bytes &= 0xfffffffc;

  /* write address to CONFIG_ADDR_PORT */
  outl(ptr->bytes, CONFIG_ADDR_PORT);
  
  /* read data from CONFIG_DATA_PORT */
  data = inl(CONFIG_DATA_PORT);
  
  return data;
}

static inline void write_pci_config_dword(pci_config_reg_addr_t *ptr, u32 val)
{
  /* zero out the last two bits, in case we are sent a malformed address */
  ptr->bytes &= 0xfffffffc;
  
  /* write address to CONFIG_ADDR_PORT */
  outl(ptr->bytes, CONFIG_ADDR_PORT);

  /* write data to CONFIG_DATA_PORT */
  outl(val, CONFIG_DATA_PORT);
}

#endif /* __ASSEMBLY__ */
#endif /* __PCI_H__ */
