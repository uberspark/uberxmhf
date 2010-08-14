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

/* visor.h - TrustVisor specific definitions */

#ifndef __VISOR_H_
#define __VISOR_H_

#define ENTRY(x)\
  .globl x;	\
  .align;	\
  x:
#define ALIGN .align 4, 0x00

#define __VISOR_CS 0x0008 /* Selector for GDT entry 1. RPL 0 */
#define __VISOR_DS 0x0010 /* Selector for GDT entry 0. RPL 0 */

/* TrustVisor is loaded into physical memory at 30MB. The region between
 * 30MB and 32MB contains the initialization code and data. The region
 * between 32MB and VISOR_RUNTIME_END contains the runtime. The
 * initialization code relocates the runtime to the highest available
 * 32MB aligned physical address. 
 */
#define VISOR_RUNTIME_START 0x2000000 	/* 32MB */
/* size should be a multiple of 2MB */
#define VISOR_RUNTIME_SIZE 0x2000000 	/* 32MB */
#define VISOR_RUNTIME_END VISOR_RUNTIME_START + VISOR_RUNTIME_SIZE - 1
/* Synchronize this definition with the definition of VISOR_START_ADDRESS in 
 * loader.h
 */
#define VISOR_LOAD_START 0x1E00000 /* 30 MB */
#define VISOR_INIT_SIZE VISOR_RUNTIME_START - VISOR_LOAD_START
/* Put microcode just below visor */
#define UCODE_RELOCATE 0x1dff000
#define UCODE_MAX_SIZE 0x1000
#define VISOR_BIOS_START 0xE0000
#define VISOR_BIOS_SIZE 0x20000
#define STARTUP_STACK_SIZE 0x1000 	/* 4K byte stack for start up */
#define STACK_SIZE 0x2000 		/* 8KB stack */

/* the top address of Linux physical mapping */
#define ADDR_LINUX_TOP 0xF8000000UL

#define WHITELIST_SIZE 2 /* 8KB to hold the whitelist of module address */
#define HASHLIST_SIZE 10 /* 40KB to hold the whitelist of hashes */
#define MODBUF_SIZE 512 /* up to 2MB to hold one sections of module */
#define MODPFN_SIZE 128 /* up to 512K to cover all phyiscal pages in 4G address space */
#define INIT_STACK_RESV 64 /* reserve 64 bytes on top of init code stack */

#ifndef __ASSEMBLY__
/*  */
enum VisorScmd
{
  VISOR_SCMD_REG = 1,
  VISOR_SCMD_UNREG = 2,
  VISOR_STPM_PCRREAD = 11,
  VISOR_STPM_EXTEND = 12,
  VISOR_STPM_SEAL = 13,
  VISOR_STPM_UNSEAL = 14,
  VISOR_STPM_QUOTE = 15,
  VISOR_STPM_RAND = 16,
  //  VISOR_STPM_GETPUBKEY = 17,
  VISOR_LTSTATE_GETSIZE = 100,
  VISOR_LTSTATE_GET = 101,
  VISOR_LTSTATE_PUT = 102,
  VISOR_DBG_STR = 200,
};

extern struct vmcb_struct *linux_vmcb;

/* various global variables */
extern u32 visor_relocate_address;
extern u32 is_relocated;
extern u32 visor_linux_top;
extern u32 _visor_text[], _visor_end[], _visor_data_end[];
extern u32 _visor_bss_start[], _visor_bss_end[];
extern u32 _visor_init_edata[];
extern u32 guest_cr0, guest_cr3;

void init_visor_pt(void);
void init_shadow_pt(void);

/* general help functions to setup bit vector */
void set_prot(u32 pa, u32 size, u8 *bit_vector);
void clear_prot(u32 pa, u32 size, u8 *bit_vector);
u32 test_prot(u32 pa, u32 size, u8 *bit_vector);

/* address translation in TrustVisor's addrss space
 */
static inline u32 __va(u32 x)
{
  if(!is_relocated)
    return (u32)(x);
  return (u32)(((x) - visor_relocate_address) + VISOR_RUNTIME_START);
}

static inline u32 __pa(u32 x)
{
  if(!is_relocated)
    return (u32)(x);
  return (u32)(((x) - VISOR_RUNTIME_START) + visor_relocate_address);
}

/* converts guest physical address to host virtual address 
 * remember: only used when PAGING enabled
 */
static inline void* __gpa2hva(u32 x)
{
  if (((x) < VISOR_RUNTIME_START) || ((x) >= VISOR_RUNTIME_END))
    return (void*)(x);
  return (void*)(((x) - VISOR_RUNTIME_START) + visor_relocate_address);
}

/* decide whether or not cache is disabled */
#define CACHE_DISABLED(cr0)		(cr0 & CR0_CD)

/* Cache disabled is not a common case, and at least we only find it
 * necessary for mtrr settings, so, we don't need to optimize this too
 * much, just make sure it is correct. Right ? 
 */
#define VMCB_PRE_SYNC(guest_cr0)			\
  ({						\
     if (CACHE_DISABLED(guest_cr0))		\
     {						\
       CACHE_WBINV();				\
     }						\
  })

#define VMCB_POST_SYNC(guest_cr0)		\
  ({						\
     if (CACHE_DISABLED(guest_cr0)) 		\
     {						\
       CACHE_WBINV();				\
     }						\
  })

/* helper function to setup bit vector */
static inline void set_page_prot(u32 pfn, u8 *bit_vector)
{
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] |= (1 << bit_offset);

  return;
}

static inline void clear_page_prot(u32 pfn, u8 *bit_vector)
{
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  bit_vector[byte_offset] &= ~(1 << bit_offset);

  return;
}

static inline u32 test_page_prot(u32 pfn, u8 *bit_vector)
{
  u32 byte_offset, bit_offset;

  byte_offset = pfn / 8;
  bit_offset = pfn & 7;
  if (bit_vector[byte_offset] & (1 << bit_offset))
    return 1;
  else 
    return 0;
}

/* help function to setup io permission bit vector */
static inline void iopm_set_write(u32 port, u32 size)
{
  extern u8 visor_io_perm_bitmap[];
  u32 i;

  for (i = 0; i < size; i ++)
    set_page_prot(port, visor_io_perm_bitmap);
}

#endif /* __ASSEMBLY__ */

#endif /* __VISOR_H_ */
