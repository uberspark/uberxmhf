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

/* dev.h definitions and declarations for AMD DEV 
 * Written for TrustVisor by Arvind Seshadri
 */

#ifndef __DEV_H__
#define __DEV_H__

/* location of DEV capability block in PCI config space */
/* FIXME: this location is probably only valid on the Sahara system.
 * In general, we will have to perform a PCI config space probe 
 * to discover the correct location.  
 * From AMD BKDG, "Coherent HyperTransport device configuration space is 
 * accessed by using Bus 0, devices 24 to 31, where Device 24 corresponds 
 * to Node 0 and Device 31 corresponds to Node 7." Therefore, AMD K8 
 * Miscellaneous Control on CPU 0 will always be mapped to Bus 0, Device 24, 
 * Function 3. The DEV capability block is part of the Miscellaneous Control
 * configuration space. So, we can safely assume that this location will
 * be the same on all AMD K8s.
 */
#define DEV_PCI_DEVICE_ID_SAHARA 0x12031022
#define DEV_PCI_DEVICE_ID 0x11031022

#define DEV_BUS        0
#define DEV_DEVICE     24
#define DEV_FUNCTION   3

/* Register offsets in DEV capability block */
/* FIXME: Will these offsets change between CPU families? */
#define DEV_HDR  0x0
#define DEV_OP   0x4
#define DEV_DATA 0x8

/* bit 17 of DEV_HDR indicates support for DEV */
#define CAP_ID 0x0f
/* bit 16-18 should be 010b in SPEC, but it seems to be 0 in real Opetron */
#define DEV_CAP_BITS 0

/* Log (base 2) of the bytes of physical memory covered by each bit 
 * in the DEV bit vector 
 */
#define LG_BASE2_BYTES_PER_DEV_BIT 12 

/* DEV_OP function codes */
#define DEV_BASE_LO     0
#define DEV_BASE_HI     1
#define DEV_MAP         2
#define DEV_CAP         3
#define DEV_CR          4
#define DEV_ERR_STATUS  5
#define DEV_ERR_ADDR_LO 6
#define DEV_ERR_ADDR_HI 7


#ifndef __ASSEMBLY__
extern u32 dev_capoff;
extern u32 init_dev_capoff;
extern u8 dev_bit_vector[];
extern u8 init_dev_bit_vector[];

/* DEV_HDR fields */
typedef union dev_hdr
{
  u32 bytes;
  struct{
    u32 cap_id:8; /* Bits 0-7 Capability ID */
    u32 cap_ptr:8; /* Bits 8-15 Pointer to next capability block */
    u32 cap_type:3; /*Bits 16-18 DEV Capability Block Type */
    u32 resv1:1; /* Bit 19 reserved */
    u32 mce_cap:1; /* Bit 20 Machine check exception reporting capability */
    u32 int_cap:1; /* Bit 21 Interrupt reporting capability */
    u32 resv2:10; /* Bits 22-31 reserved */
  }fields;
} __attribute__ ((packed)) dev_hdr_t;

typedef union dev_cap 
{
  u32 bytes;
  struct{
    u32 rev:8; /* bits 0-7 implementatin revision */
    u32 n_dom:8; /* bits 8-15 number of domains supported */
    u32 n_maps:8; /*bits 16-24 number of map registers supported */
    u32 resv:8; /* bits 25-31 reserved */
  }fields;
} __attribute__ ((packed)) dev_cap_t;

typedef union dev_cr
{
  u32 bytes;
  struct{
    u32 enable:1; /* bit 0: dev enable */
    u32 mem_clr:1; /* bit 1: set to disable memory clear on reset */
    u32 iospen:1; /* bit 2: set to disable upstream i/o cycles */
    u32 mce_en:1; /*bit 3: set to generate MCE on errors */
    u32 invl:1; /* bit 4: set to invalidate DEV cache */
    u32 sl_dev_en:1; /* bit 5: set by skinit to protect SLB memory */
    u32 walk_probe:1; /* bit 6: set to disable DEV table walk probes */
    u32 resv:25; /* bits 7-31: reserved */
  }fields;
} __attribute__ ((packed)) dev_cr_t;

typedef union dev_base_hi
{
  u32 bytes;
  struct{
    u32 base_addr:8; /* bits 0-7: bits 39-32 of DEV base address */
    u32 resv:24; /* bits 8-31: reserved */
  }fields;
} __attribute__ ((packed)) dev_base_hi_t;

typedef union dev_base_low
{
  u32 bytes;
  struct{
    u32 valid:1; /* bit 0: set to add DEV protection for a domain */
    u32 protect:1; /* bit 1: accesses to addresses beyond DEV range valid? */
    u32 size:5; /* bits 2-6: size of memory protected by the DEV */
    u32 resv:5; /* bits 7-11: reserved */
    u32 base_addr:20; /* bits 12-31: bits 12-31 of DEV base address */
  }fields;
} __attribute__ ((packed)) dev_base_low_t;

typedef union dev_map
{
  u32 bytes;
  struct{
    u32 unit0:5; /* bits 0-4: hypertransport link unit number */
    u32 v0:1; /* bit 5: valid 0 */
    u32 unit1:5; /* bits 6-10: hypertransport link unit number */
    u32 v1:1; /* bit 11: valid 1 */
    u32 bus_no:8; /* bits 12-19: hypertransport link bus number */
    u32 dom0:6; /* bits 20-25: domain unit 0 is mapped to */
    u32 dom1:6; /* bits 26-31: domain unit 1 is mapped to */
  }fields;
} __attribute__ ((packed)) dev_map_t;

/* read DEV function registers. pass 0 in index if there no index */
static inline u32 read_dev_fn(u32 function, u32 index)
{
  u32 data;
  pci_config_reg_addr_t config_reg;
  
  /* first write function and index to DEV_OP reg */
  data = ((function & 0xff) << 8) + (index & 0xff);
  config_reg.bytes = 0;
  config_reg.fields.offset = dev_capoff + DEV_OP;
  config_reg.fields.function = DEV_FUNCTION;
  config_reg.fields.device = DEV_DEVICE;
  config_reg.fields.bus = DEV_BUS;
  config_reg.fields.enabled = 1;
  
  write_pci_config_dword(&config_reg, data);
  
  /* then read DEV_DATA reg */
  config_reg.fields.offset = dev_capoff + DEV_DATA;
  data = read_pci_config_dword(&config_reg);
  
  return (data);
}

/* write DEV function registers. pass 0 in index if there no index */
static inline void write_dev_fn(u32 function, u32 index, u32 val)
{
  u32 data;
  pci_config_reg_addr_t config_reg;
  
  /* first write function and index to DEV_OP reg */
  data = ((function & 0xff) << 8) + (index & 0xff);
  config_reg.bytes = 0;
  config_reg.fields.offset = dev_capoff + DEV_OP;
  config_reg.fields.function = DEV_FUNCTION;
  config_reg.fields.device = DEV_DEVICE;
  config_reg.fields.bus = DEV_BUS;
  config_reg.fields.enabled = 1;
  
  write_pci_config_dword(&config_reg, data);
  
  /* then write DEV_DATA reg */
  config_reg.fields.offset = dev_capoff + DEV_DATA;
  write_pci_config_dword(&config_reg, val);
}

static inline void init_write_dev_fn(u32 function, u32 index, u32 val)  __attribute__ ((section ("_init_text")));

/* write DEV function registers. pass 0 in index if there no index */
static inline void init_write_dev_fn(u32 function, u32 index, u32 val)
{
  u32 data;
  pci_config_reg_addr_t config_reg;
  
  /* first write function and index to DEV_OP reg */
  data = ((function & 0xff) << 8) + (index & 0xff);
  config_reg.bytes = 0;
  config_reg.fields.offset = init_dev_capoff + DEV_OP;
  config_reg.fields.function = DEV_FUNCTION;
  config_reg.fields.device = DEV_DEVICE;
  config_reg.fields.bus = DEV_BUS;
  config_reg.fields.enabled = 1;
  
  write_pci_config_dword(&config_reg, data);
  
  /* then write DEV_DATA reg */
  config_reg.fields.offset = init_dev_capoff + DEV_DATA;
  write_pci_config_dword(&config_reg, val);
}

/* invalidate the DEV cache */
static inline void dev_cache_invalidate(void)
{
  dev_cr_t dev_cr;

  dev_cr.bytes = read_dev_fn(DEV_CR, 0);
  dev_cr.fields.invl = 1;
  write_dev_fn(DEV_CR, 0, dev_cr.bytes);

  while ( (dev_cr.bytes = read_dev_fn(DEV_CR, 0)) == 1)
    ;

  return;
}

/* set DEV protection for a page, pfn is the page frame number */
#define set_page_dev_prot(pfn)	set_page_prot(pfn, dev_bit_vector)
/* clear DEV protection for a page, pfn is the page frame number */
#define clear_page_dev_prot(pfn)  clear_page_prot(pfn, dev_bit_vector)

/* set DEV protection for a range of pages
 * pa is address of the first page
 * size is the size of the memory region in bytes 
 */
static inline void set_dev_prot(u32 pa, u32 size)
{
  set_prot(pa, size, dev_bit_vector);
  dev_cache_invalidate();
}

/* clear DEV protection for a range of pages
 * pa is address of the first page
 * size is the size of the memory region in bytes 
 */
static inline void clear_dev_prot(u32 pa, u32 size)
{
  clear_prot(pa, size, dev_bit_vector);
  dev_cache_invalidate();
}

#endif /* __ASSMEBLY__ */

#endif /* __DEV_H__ */
