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

/* pgtable.h: Macros, definitions, and functions for handling paging  
 * Written by Arvind Seshadri, Ning Qu, and Mark Luk
 * Cleaned up by Arvind Seshadri
 */

#ifndef __PGTABLE_H__
#define __PGTABLE_H__

/* Limits of user and kernel memory in 32-bit Linux */
#ifndef __ASSEMBLY__
#define ADDR_4GB 0x100000000ULL 	/* Arvind: LINUX_KERNEL_END better? */
#define ADDR_3GB 0xC0000000UL 		/* Arvind: LINUX_USER_END better? */
#define LAST_PHY_ADDR 0xffffffffUL
#else
#define ADDR_4GB 0x100000000
#define ADDR_3GB 0xC0000000
#define LAST_PHY_ADDR 0xffffffff
#endif

/* various page sizes */
#ifndef __ASSEMBLY__
#define PAGE_SIZE_4K (1UL << 12)
#define PAGE_SIZE_2M (1UL << 21)
#define PAGE_SIZE_4M (1UL << 22)
#else   
#define PAGE_SIZE_4K (1 << 12)
#define PAGE_SIZE_2M (1 << 21)
#define PAGE_SIZE_4M (1 << 22)
#endif

#define PAGE_SHIFT_4K 12
#define PAGE_SHIFT_2M 21

#define PAGE_ALIGN_UP4K(size)	(((size) + PAGE_SIZE_4K - 1) & ~(PAGE_SIZE_4K - 1))
#define PAGE_ALIGN_4K(size)	((size) & ~(PAGE_SIZE_4K - 1))
#define PAGE_ALIGN_2M(size)	((size) & ~(PAGE_SIZE_2M - 1))
#define PAGE_ALIGN_4M(size)	((size) & ~(PAGE_SIZE_4M - 1))
/* non-PAE mode specific definitions */
#define NPAE_PTRS_PER_PDT       1024
#define NPAE_PTRS_PER_PT        1024
#define NPAE_PAGETABLE_SHIFT    12
#define NPAE_PAGEDIR_SHIFT      22
#define NPAE_PAGE_DIR_MASK      0xffc00000
#define NPAE_PAGE_TABLE_MASK    0x003ff000

/* PAE mode specific definitions */
#define PAE_PTRS_PER_PDPT  4
#define PAE_PTRS_PER_PDT   512
#define PAE_PTRS_PER_PT    512
#define PAE_PT_SHIFT       12
#define PAE_PDT_SHIFT      21
#define PAE_PDPT_SHIFT     30
#define PAE_PT_MASK        0x001ff000
#define PAE_PDT_MASK       0x3fe00000
#define PAE_PDPT_MASK      0xc0000000
#define PAE_ENTRY_SIZE     8

/* various paging flags */
#define _PAGE_BIT_PRESENT	0
#define _PAGE_BIT_RW		1
#define _PAGE_BIT_USER		2
#define _PAGE_BIT_PWT		3
#define _PAGE_BIT_PCD		4
#define _PAGE_BIT_ACCESSED	5
#define _PAGE_BIT_DIRTY		6
#define _PAGE_BIT_PSE		7	/* 2MB page */
#define _PAGE_BIT_GLOBAL	8	/* Global TLB entry */
#define _PAGE_BIT_UNUSED1	9	/* available for programmer */
#define _PAGE_BIT_UNUSED2	10
#define _PAGE_BIT_UNUSED3	11
#define _PAGE_BIT_NX		63

#define _PAGE_PRESENT	0x001
#define _PAGE_RW	0x002   /*0 is readonly, 1 is RW */
#define _PAGE_USER	0x004
#define _PAGE_PWT	0x008
#define _PAGE_PCD	0x010
#define _PAGE_ACCESSED	0x020
#define _PAGE_DIRTY	0x040
#define _PAGE_PSE	0x080	/* 2MB page */
#define _PAGE_GLOBAL	0x100	/* Global TLB entry */
#define _PAGE_UNUSED1	0x200	/* available for programmer */
#define _PAGE_UNUSED2	0x400
#define _PAGE_UNUSED3	0x800
#ifndef __ASSEMBLY__
#define _PAGE_NX	(1ULL<<_PAGE_BIT_NX)
#else
#define _PAGE_NX        (1 << _PAGE_BIT_NX)
#endif 

#define PAGE_FAULT_BITS (_PAGE_PRESENT | _PAGE_RW | _PAGE_USER | _PAGE_NX)

#define ASID_GUEST 1

/* move all this into a shadow_area.h? */

#ifndef __ASSEMBLY__

typedef u64 *pdpt_t; 
typedef u64 *pdt_t;
typedef u64 *pt_t;

typedef u32 *npdt_t;
typedef u32 *npt_t;

/* make a page directory pointer entry from individual fields */
#define pae_make_pdpe(paddr, flags) \
  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))) | (u64)(flags)

/* make a page directory entry for a 2MB page from individual fields */
#define pae_make_pde_big(paddr, flags) \
  ((u64)(paddr) & (~(((u64)PAGE_SIZE_2M - 1) | _PAGE_NX))) | (u64)(flags)

/* make a page directory entry for a 4KB page from individual fields */
#define pae_make_pde(paddr, flags) \
  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))) | (u64)(flags)

/* make a page table entry from individual fields */
#define pae_make_pte(paddr, flags) \
  ((u64)(paddr) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))) | (u64)(flags)

/* get address field from 32-bit cr3 (page directory pointer) in PAE mode */
#define pae_get_addr_from_32bit_cr3(entry) \
  ((u32)(entry) & (~((1UL << 5) - 1))) 

/* get flags field from 32-bit cr3 (page directory pointer) in PAE mode */
#define pae_get_flags_from_32bit_cr3(entry) \
  ((u32)(entry) & ((1UL << 5) - 1)) 

/* get address field of a pdpe (page directory pointer entry) */
#define pae_get_addr_from_pdpe(entry) \
  ((u64)(entry) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))) 

/* get flags field of a pdpe (page directory pointer entry) */
#define pae_get_flags_from_pdpe(entry) \
  ((u64)(entry) & (((u64)PAGE_SIZE_4K - 1) | _PAGE_NX)) 

/* get address field of a 2MB pdte (page directory entry) */
#define pae_get_addr_from_pde_big(entry) \
  ((u64)(entry) & (~(((u64)PAGE_SIZE_2M - 1) | _PAGE_NX)))

/* get flags field of a 2MB pdte (page directory entry) */
#define pae_get_flags_from_pde_big(entry) \
  ((u64)(entry) & (((u64)PAGE_SIZE_2M - 1) | _PAGE_NX))

/* get address field of a 4K pdte (page directory entry) */
#define pae_get_addr_from_pde(entry) \
  ((u64)(entry) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX)))

/* get flags field of a 4K pdte (page directory entry) */
#define pae_get_flags_from_pde(entry) \
  ((u64)(entry) & (((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))

/* get address field of a pte (page table entry) */
#define pae_get_addr_from_pte(entry) \
  ((u64)(entry) & (~(((u64)PAGE_SIZE_4K - 1) | _PAGE_NX)))

/* get flags field of a pte (page table entry) */
#define pae_get_flags_from_pte(entry) \
  ((u64)(entry) & (((u64)PAGE_SIZE_4K - 1) | _PAGE_NX))

/* make a page directory entry for a 4MB page from individual fields */
#define npae_make_pde_big(paddr, flags) \
  ((u32)(paddr) & (~(((u32)PAGE_SIZE_4M - 1) | _PAGE_NX))) | (u32)(flags)

/* make a page directory entry for a 4KB page from individual fields */
#define npae_make_pde(paddr, flags) \
  ((u32)(paddr) & (~(((u32)PAGE_SIZE_4K - 1) | _PAGE_NX))) | (u32)(flags)

/* get address field from NON-PAE cr3 (page directory pointer) */
#define npae_get_addr_from_32bit_cr3(entry) \
  ((u32)(entry) & (~((u32)PAGE_SIZE_4K - 1))) 

/* get address field of a 4K non-PAE pdte (page directory entry) */
#define npae_get_addr_from_pde(entry) \
  ((u32)(entry) & (~((u32)PAGE_SIZE_4K - 1)))

/* get flags field of a 4K non-PAE pdte (page directory entry) */
#define npae_get_flags_from_pde(entry) \
  ((u32)(entry) & ((u32)PAGE_SIZE_4K - 1))

/* get address field of a 4M (non-PAE) pdte (page directory entry) */
#define npae_get_addr_from_pde_big(entry) \
  ((u32)(entry) & (~((u32)PAGE_SIZE_4M - 1)))

/* get flags field of a 4M (non-PAE) pdte (page directory entry) */
#define npae_get_flags_from_pde_big(entry) \
  ((u32)(entry) & ((u32)PAGE_SIZE_4M - 1))

/* get address field of a 4K (non-PAE) pte (page table entry) */
#define npae_get_addr_from_pte(entry) \
  ((u32)(entry) & (~((u32)PAGE_SIZE_4K - 1)))

/* get page offset field of a vaddr in a 4K page (PAE mode) */
#define pae_get_offset_4K_page(entry) \
  ((u32)(entry) & ((u32)PAGE_SIZE_4K - 1))

/* get page offset field of a vaddr in a 2M page */
#define pae_get_offset_big(entry) \
  ((u32)(entry) & ((u32)PAGE_SIZE_2M - 1))

/* get offset field of a vaddr in a 4K page (non-PAE mode) */
#define npae_get_offset_4K_page(vaddr) \
  ((u32)(vaddr) & ((u32)PAGE_SIZE_4K - 1))

/* get offset field of a vaddr in a 4M page */
#define npae_get_offset_big(vaddr) \
  ((u32)(vaddr) & ((u32)PAGE_SIZE_4M - 1))

/* get index field of a paddr in a pdp level */
#define pae_get_pdpt_index(paddr)\
    (((paddr) & PAE_PDPT_MASK) >> PAE_PDPT_SHIFT)

/* get index field of a paddr in a pd level */
#define pae_get_pdt_index(paddr)\
    (((paddr) & PAE_PDT_MASK) >> PAE_PDT_SHIFT)

/* get index field of a paddr in a pt level */
#define pae_get_pt_index(paddr)\
    (((paddr) & PAE_PT_MASK) >> PAE_PT_SHIFT)

/* get index field of a paddr in a pd level */
#define npae_get_pdt_index(paddr)\
    (((paddr) & NPAE_PAGE_DIR_MASK) >> NPAE_PAGEDIR_SHIFT)

/* get index field of a paddr in a pt level */
#define npae_get_pt_index(paddr)\
    (((paddr) & NPAE_PAGE_TABLE_MASK) >> NPAE_PAGETABLE_SHIFT)

/* returns 1 if addr is 4k page aligned */
#define is_page_4K_aligned(paddr)\
    ((((u32)PAGE_SIZE_4K - 1) & ((u32)paddr)) == 0)

#define set_exec(entry) (((u64)entry) &= (~((u64)_PAGE_NX)))
#define set_nonexec(entry) (((u64)entry) |= ((u64)_PAGE_NX))
#define set_readonly(entry) (((u64)entry) &= (~((u64)_PAGE_RW)))
#define set_readwrite(entry) (((u64)entry) |= ((u64)_PAGE_RW))
#define set_present(entry) (((u64)entry) |= ((u64)_PAGE_PRESENT))
#define set_not_present(entry) (((u64)entry) &= (~((u64)_PAGE_PRESENT)))

#define SAME_PAGE_PAE(addr1, addr2)		\
    (((addr1) >> PAE_PT_SHIFT) == ((addr2) >> PAE_PT_SHIFT))

#define SAME_PAGE_NPAE(addr1, addr2)		\
    (((addr1) >> NPAE_PAGETABLE_SHIFT) == ((addr2) >> NPAE_PAGETABLE_SHIFT))

/* various funtions for TLB flush */
#define VMCB_TLB_NOTHING() ({ linux_vmcb->tlb_control = TLB_CONTROL_NOTHING; })
#define VMCB_TLB_FLUSHALL() ({linux_vmcb->tlb_control = TLB_CONTROL_FLUSHALL; })

#define TLB_FLUSH_ALL		VMCB_TLB_FLUSHALL

#define TLB_FLUSH()			\
  ({					\
     u32 value;				\
     if (!(linux_vmcb->cr4 & CR4_PGE))	\
     {					\
       VMCB_TLB_FLUSHALL();		\
     }else				\
     {					\
       value = read_cr3();		\
       write_cr3(value);		\
     }					\
  })

#define TLB_FLUSH_ENTRY(addr)		\
  ({					\
     u32 value;			\
     if (!(linux_vmcb->cr4 & CR4_PGE))	\
     {					\
       value = read_cr4();		\
       write_cr4(value & (u32)~(CR4_PGE));		\
  					\
       TLB_INVLPG(addr);		\
  					\
       write_cr4(value);		\
     }else				\
     {					\
       TLB_INVLPG(addr);		\
     }					\
  })

#define CACHE_WBINV()  __asm__ __volatile__("wbinvd\n" :::"memory")
#define TLB_INVLPG(x) __asm__ __volatile__("invlpg (%0)\n": /* no output */ : "r" (x): "memory")

/* Calls to read and write control registers */ 
static inline unsigned long read_cr0(void)
{
  unsigned long __cr0;
  __asm__("mov %%cr0,%0\n\t" :"=r" (__cr0));
  return __cr0;
}

static inline void write_cr0(unsigned long val)
{
  __asm__("mov %0,%%cr0": :"r" ((unsigned long)val));
}

static inline unsigned long read_cr3(void)
{
  unsigned long __cr3;
  __asm__("mov %%cr3,%0\n\t" :"=r" (__cr3));
  return __cr3;
}

static inline void write_cr3(unsigned long val)
{
  __asm__("mov %0,%%cr3\n\t"
          "jmp 1f\n\t"
          "1:"
          : 
          :"r" ((unsigned long)val));
}

static inline unsigned long read_cr2(void)
{
  unsigned long __cr2;
  __asm__("mov %%cr2,%0\n\t" :"=r" (__cr2));
  return __cr2;
}

static inline unsigned long read_cr4(void)
{
  unsigned long __cr4;
  __asm__("mov %%cr4,%0\n\t" :"=r" (__cr4));
  return __cr4;
}

static inline void write_cr4(unsigned long val)
{
  __asm__("mov %0,%%cr4": :"r" ((unsigned long)val));
}

/* nested paging handlers */
void init_nested_paging(void);
void activate_nested_paging(void);

void nested_set_prot(u32 pfn, int type);
void nested_clear_prot(u32 pfn);
void nested_promote(u32 pfn);
int guest_pt_copy(u32 pte_page, u64 gcr3, u32 gvaddr, u32 size, int type);
void nested_switch_scode(u32 pte_page, u32 size, u32 pte_page2, u32 size2);
void nested_switch_regular(u32 pte_page, u32 size, u32 pte_page2, u32 size2);

/* some public helper function which should be implemented by both shadow
 * paging and nested paging
 */
#define guest_pt_walker(gcr3, vaddr)	guest_pt_walker_internal(gcr3, vaddr, NULL, NULL, NULL)

u32 guest_pt_walker_internal(u64 gcr3, u32 vaddr, u64 *pdp, u64 *pd, u64 *pt);

/* several help functions to access guest address space */
static inline u16 get_16bit_aligned_value_from_guest(u64 gcr3, u32 gvaddr)
{
  u32 gpaddr;
  
  gpaddr = guest_pt_walker(gcr3, gvaddr);
  return *((u16 *)__gpa2hva(gpaddr));
}

static inline u32 get_32bit_aligned_value_from_guest(u64 gcr3, u32 gvaddr)
{
  u32 gpaddr;
  
  gpaddr = guest_pt_walker(gcr3, gvaddr);
  return *((u32 *)__gpa2hva(gpaddr));
}

static inline void put_32bit_aligned_value_to_guest(u64 gcr3, u32 gvaddr, u32 value)
{
  u32 gpaddr;
  
  gpaddr = guest_pt_walker(gcr3, gvaddr);
  *((u32 *)__gpa2hva(gpaddr)) = value;
}

static inline void copy_from_guest(u8 *dst, u64 gcr3, u32 gvaddr, u32 len)
{
  u32 gpaddr, gvend, gvprev;
  u32 tmp;
  
  gvprev = gvaddr;
  gvend = gvaddr + len;

  gpaddr = guest_pt_walker(gcr3, gvaddr);

  if (gvaddr & 0x3)
  {
    tmp = (gvaddr + 0x3) & (u32)~0x3;
    for (; (gvaddr < gvend) && (gvaddr < tmp); gvaddr ++, gpaddr ++, dst ++)
    {
      if (!SAME_PAGE_NPAE(gvprev, gvaddr))
        gpaddr = guest_pt_walker(gcr3, gvaddr);

      *dst = *((u8 *)__gpa2hva(gpaddr));
      gvprev = gvaddr;
    }
  }
  if (gvaddr < gvend)
  {
    tmp = gvend & (u32)~0x3;
    for (; gvaddr < tmp; gvaddr += 4, gpaddr += 4, dst += 4)
    {
      if (!SAME_PAGE_NPAE(gvprev, gvaddr))
        gpaddr = guest_pt_walker(gcr3, gvaddr);

      *(u32 *)dst = *((u32 *)__gpa2hva(gpaddr));
      gvprev = gvaddr;
    }
  }
  if (gvaddr < gvend)
  {
    for (; gvaddr < gvend; gvaddr ++, gpaddr ++, dst ++)
    {
      if (!SAME_PAGE_NPAE(gvprev, gvaddr))
        gpaddr = guest_pt_walker(gcr3, gvaddr);

      *dst = *((u8 *)__gpa2hva(gpaddr));
      gvprev = gvaddr;
    }
  }
  return;
}

static inline void copy_to_guest(u64 gcr3, u32 gvaddr, u8 *src, u32 len)
{
  u32 gpaddr, gvend, gvprev;
  u32 tmp;
  
  gvprev = gvaddr;
  gvend = gvaddr + len;

  gpaddr = guest_pt_walker(gcr3, gvaddr);

  if (gvaddr & 0x3)
  {
    tmp = (gvaddr + 0x3) & (u32)~0x3;
    for (; (gvaddr < gvend) && (gvaddr < tmp); gvaddr ++, gpaddr ++, src ++)
    {
      if (!SAME_PAGE_NPAE(gvprev, gvaddr))
        gpaddr = guest_pt_walker(gcr3, gvaddr);

      *((u8 *)__gpa2hva(gpaddr)) = *src;
      gvprev = gvaddr;
    }
  }
  if (gvaddr < gvend)
  {
    tmp = gvend & (u32)~0x3;
    for (; gvaddr < tmp; gvaddr += 4, gpaddr += 4, src += 4)
    {
      if (!SAME_PAGE_NPAE(gvprev, gvaddr))
        gpaddr = guest_pt_walker(gcr3, gvaddr);

      *((u32 *)__gpa2hva(gpaddr)) = *(u32 *)src;
      gvprev = gvaddr;
    }
  }
  if (gvaddr < gvend)
  {
    for (; gvaddr < gvend; gvaddr ++, gpaddr ++, src ++)
    {
      if (!SAME_PAGE_NPAE(gvprev, gvaddr))
        gpaddr = guest_pt_walker(gcr3, gvaddr);

      *((u8 *)__gpa2hva(gpaddr)) = *src;
      gvprev = gvaddr;
    }
  }
  return;
}

#endif /* __ASSEMBLY__ */

#endif /* __PGTABLE_H__ */
