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

//pci configuration access
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __PCI_H__
#define __PCI_H__

/* PCI config space ports */
#define PCI_CONFIG_ADDR_PORT (u16)0x0cf8
#define PCI_CONFIG_DATA_PORT (u16)0x0cfc

#define PCI_CONF_HDR_ID 0x0
#define PCI_CONF_HDR_CMD 0x4
#define PCI_CONF_HDR_CAP 0x34

#define PCI_CAP_OFFSET 0x1

#define PCI_VENDOR_ID           0x00    /* 16 bits */
#define PCI_DEVICE_ID           0x02    /* 16 bits */
#define PCI_COMMAND             0x04    /* 16 bits */
#define PCI_STATUS              0x06    /* 16 bits */

#define PCI_BASE_ADDRESS_0      0x10    /* 32 bits */
#define PCI_BASE_ADDRESS_1      0x14    /* 32 bits [htype 0,1 only] */
#define PCI_BASE_ADDRESS_2      0x18    /* 32 bits [htype 0 only] */
#define PCI_BASE_ADDRESS_3      0x1c    /* 32 bits */
#define PCI_BASE_ADDRESS_4      0x20    /* 32 bits */
#define PCI_BASE_ADDRESS_5      0x24    /* 32 bits */


#define PCI_VENDOR_ID           0x00    /* 16 bits */
#define PCI_DEVICE_ID           0x02    /* 16 bits */
#define PCI_COMMAND             0x04    /* 16 bits */
#define PCI_COMMAND_IO          0x1     /* Enable response in I/O space */
#define PCI_COMMAND_MEMORY      0x2     /* Enable response in Memory space */
#define PCI_COMMAND_MASTER      0x4     /* Enable bus mastering */
#define PCI_COMMAND_SPECIAL     0x8     /* Enable response to special cycles */
#define PCI_COMMAND_INVALIDATE  0x10    /* Use memory write and invalidate */
#define PCI_COMMAND_VGA_PALETTE 0x20   /* Enable palette snooping */
#define PCI_COMMAND_PARITY      0x40    /* Enable parity checking */
#define PCI_COMMAND_WAIT        0x80    /* Enable address/data stepping */
#define PCI_COMMAND_SERR        0x100   /* Enable SERR */
#define PCI_COMMAND_FAST_BACK   0x200   /* Enable back-to-back writes */
#define PCI_COMMAND_INTX_DISABLE 0x400 /* INTx Emulation Disable */


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


typedef struct {
  u32 baseAddress;
  u32 size;
  u8 prefetchable;
  u8 type; //mem or I/O
  u8 location; //0 = anywhere in 32-bit, 1 = below 1M, 2 = anywhere
                          // in 64-bit
  u8 inuse;
} __attribute__ ((packed)) pci_configheader_bar_t;


typedef struct {
  u16 vendorId;
  u16 deviceId;
  u16 command;
  u16 status;
  u8 revision;
  u8 classCode;
  u8 subclassCode;
  u8 progIf;
  u8 cacheLineSize;
  u8 latency;
  u8 header;
  u8 selftest;
  pci_configheader_bar_t bar[6];
  u32 cardbusInfoPtr;
  u16 subsystemVendorId;
  u16 subsystemId;
  u32 romAddress;
  u32 romSize;
  u8 irqLine;
  u8 intPin;
  u8 minGrant;
  u8 maxLatency;
} __attribute__ ((packed)) pci_configheader_t;



static inline u32 read_pci_config_dword(pci_config_reg_addr_t *ptr){
  u32 data;
  
  ptr->fields.enabled=1;

  /* write address to CONFIG_ADDR_PORT */
  outl(ptr->bytes, PCI_CONFIG_ADDR_PORT);
  
  /* read data from CONFIG_DATA_PORT */
  data = inl(PCI_CONFIG_DATA_PORT);
  
  return data;
}

static inline u8 read_pci_config_byte(pci_config_reg_addr_t *ptr){
  u8 data;
  
  ptr->fields.enabled=1;

  /* write address to CONFIG_ADDR_PORT */
  outl(ptr->bytes, PCI_CONFIG_ADDR_PORT);
  
  /* read data from CONFIG_DATA_PORT */
  data = inb(PCI_CONFIG_DATA_PORT);
  
  return data;
}

static inline u16 read_pci_config_word(pci_config_reg_addr_t *ptr){
  u16 data;
  
  ptr->fields.enabled=1;
  
  /* write address to CONFIG_ADDR_PORT */
  outl(ptr->bytes, PCI_CONFIG_ADDR_PORT);
  
  /* read data from CONFIG_DATA_PORT */
  data = inw(PCI_CONFIG_DATA_PORT);
  
  return data;
}


static inline void write_pci_config_dword(pci_config_reg_addr_t *ptr, u32 val){
  ptr->fields.enabled=1;
  
  /* write address to CONFIG_ADDR_PORT */
  outl(ptr->bytes, PCI_CONFIG_ADDR_PORT);

  /* write data to CONFIG_DATA_PORT */
  outl(val, PCI_CONFIG_DATA_PORT);
}


static inline void write_pci_config_word(pci_config_reg_addr_t *ptr, u16 val){
  ptr->fields.enabled=1;
  
  /* write address to CONFIG_ADDR_PORT */
  outl(ptr->bytes, PCI_CONFIG_ADDR_PORT);

  /* write data to CONFIG_DATA_PORT */
  outw(val, PCI_CONFIG_DATA_PORT);
}

static inline void pci_set_master(pci_config_reg_addr_t *dev){
        u16 cmd;

				dev->fields.offset=PCI_COMMAND;
        cmd = read_pci_config_word(dev);
        cmd |= PCI_COMMAND_MASTER;
        dev->fields.offset=PCI_COMMAND;
        write_pci_config_word(dev, cmd);
}

static inline void pci_disable_master(pci_config_reg_addr_t *dev){
        u16 cmd;

				dev->fields.offset=PCI_COMMAND;
        cmd = read_pci_config_word(dev);
        cmd &= ~PCI_COMMAND_MASTER;
        dev->fields.offset=PCI_COMMAND;
        write_pci_config_word(dev, cmd);
}

#endif /* __ASSEMBLY__ */
#endif /* __PCI_H__ */
