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

/* hpt.h - hypervisor page table abstraction
 * author - Jim Newsome (jnewsome@cmu.edu)
 *
 * We provide here some macros for abstracting out the differences
 * between AMD's NPT and Intel's EPT. The goal is to provide just
 * enough abstraction to abstract over those two. It's not necessarily
 * possible to support additional page table structures here without
 * changing the interfaces.
 *
 * This code is intended to be side-effect free, and decoupled from
 * the details of the emhf hypervisor. They do not access global
 * state, including page table structures. They also do not manipulate
 * parameters in place; instead they return a new value.
 */

#ifndef HPT_H
#define HPT_H

#include "bitfield.h"
#include "target.h"
#include "types.h"

/* AMD and Intel disagree on the name of the 3rd level of paging
 * structures. We scrap the whole naming mess and retroactively follow
 * the lead of the recent 'pml4' 4th level, renaming the lower levels
 * pml3 through pml1.
 */
typedef u64 hpt_pml4e_t;
typedef u64 hpt_pml3e_t; /* aka pdpe or pdpte */
typedef u64 hpt_pml2e_t; /* aka pde */
typedef u64 hpt_pml1e_t; /* ake pte */

typedef u64 hpt_pme_t; /* page map entry (any level) */

typedef hpt_pml4e_t* hpt_pml4_t;
typedef hpt_pml3e_t* hpt_pml3_t;
typedef hpt_pml2e_t* hpt_pml2_t;
typedef hpt_pml1e_t* hpt_pml1_t;

typedef hpt_pme_t* hpt_pm_t; /* page map (any level) */

#define IS_INTEL(vcpu) (vcpu->cpu_vendor == CPU_VENDOR_INTEL)
#define IS_AMD(vcpu) (vcpu->cpu_vendor == CPU_VENDOR_AMD)

#define HPT_PML4_SIZE 512
#define HPT_PML3_SIZE 512
#define HPT_PML2_SIZE 512
#define HPT_PML1_SIZE 512

/* Abstract protection flags. */
#define HPT_PROT_READ (1<<0ull)
#define HPT_PROT_WRITE (1<<1ull)
#define HPT_PROT_EXEC (1<<2ull)

#define HPT_PROTS_RWX (HPT_PROT_READ|HPT_PROT_WRITE|HPT_PROT_EXEC)
#define HPT_PROTS_RW (HPT_PROT_READ|HPT_PROT_WRITE)
#define HPT_PROTS_RX (HPT_PROT_READ|HPT_PROT_EXEC)
#define HPT_PROTS_R (HPT_PROT_READ)
#define HPT_PROTS_WX (HPT_PROT_WRITE|HPT_PROT_EXEC)
#define HPT_PROTS_W (HPT_PROT_WRITE)
#define HPT_PROTS_X (HPT_PROT_EXEC)
#define HPT_PROTS_NONE (0)

#define MAX(x, y) (((y) > (x)) ? (y) : (x))
#define MIN(x, y) (((y) < (x)) ? (y) : (x))

static inline hpt_pme_t hpt_setprot(u32 cpu_vendor, hpt_pme_t entry, hpt_pme_t perms)
{
  hpt_pme_t rv=0;
  if (cpu_vendor == CPU_VENDOR_INTEL) {
    rv = BR64_SET_HL(entry, 2, 0, perms);
  } else if (cpu_vendor == CPU_VENDOR_AMD) {
    rv = BR64_SET_HL(entry, 1, 0, BR64_GET_HL(perms, 1, 0));
    rv = BR64_SET_BIT(rv, 63, BR64_GET_BIT(perms, 2) ? 0ull : 1ull);
  } else {
    ASSERT(0);
  }
  return rv;
}

static inline hpt_pme_t hpt_getprot(u32 cpu_vendor, hpt_pme_t entry)
{
  hpt_pme_t rv=0;
  if (cpu_vendor == CPU_VENDOR_INTEL) {
    rv = BR64_GET_HL(entry, 2, 0);
  } else if (cpu_vendor == CPU_VENDOR_AMD) {
    rv = BR64_GET_HL(entry, 1, 0);
    rv = BR64_SET_BIT(rv, 2, BR64_GET_BIT(entry, 63) ? 0ull : 1ull);
  } else {
    ASSERT(0);
  }
  return rv;
}

static inline hpt_pme_t hpt_setunused(u32 cpu_vendor, hpt_pme_t entry, int hi, int lo, hpt_pme_t val)
{
  hpt_pme_t rv=entry;
  ASSERT(hi>lo);

  ASSERT(cpu_vendor == CPU_VENDOR_INTEL
         || cpu_vendor == CPU_VENDOR_AMD);

  /* we map bits 2-0 to 11-9, which are unused in all
     levels of ept and npt */
  if (lo <= 2) {
    rv = BR64_COPY_BITS_HL(rv, val, MIN(2,hi), MAX(0,lo), (9-0));
  }

  /* we map bits 13-3 to 62-52 */
  if (hi >= 3) {
    rv = BR64_COPY_BITS_HL(rv, val, MIN(13,hi), MAX(3,lo), (52-3));
  }

  /* no more bits */
  /* actually, if needed we can use bit 63 on Intel and bit 8 on AMD.
   * For simplicity we won't bother utilizing these unless we need to.
   */
  ASSERT(hi <= 13);

  return rv;
}

static inline hpt_pme_t hpt_getunused(u32 cpu_vendor, hpt_pme_t entry, int hi, int lo)
{
  hpt_pme_t rv = 0ull;
  ASSERT(hi>lo);
  ASSERT(hi <= 2); /* higher bits not yet implemented */
  
  if (lo <= 2) {
    rv = BR64_GET_HL(entry, 11, 9);
  }

  return rv;
}

static inline bool hpt_is_present(u32 cpu_vendor, hpt_pme_t entry)
{
  /* a valid entry is present iff read access is enabled. */
  return hpt_getprot(cpu_vendor, entry) & HPT_PROT_READ;
}

static inline bool hpt_is_page(u32 cpu_vendor, hpt_pme_t entry, int lvl)
{
  ASSERT(lvl >= 1 && lvl <= 4);
  return 
    lvl == 1 
    || (lvl == 2) && BR64_GET_BIT(entry, 7)
    || (lvl == 3) && BR64_GET_BIT(entry, 7)
    || (lvl == 4);
}

static inline u64 hpt_get_address(u32 cpu_vendor, hpt_pme_t entry)
{
  return BR64_COPY_BITS_HL(0, entry, 51, 12, 0);
}

static inline u64 hpt_set_address(u32 cpu_vendor, hpt_pme_t entry, u64 hpa)
{
  ASSERT((hpa & MASKRANGE64(11, 0)) == 0);
  return BR64_COPY_BITS_HL(entry, hpa, 51, 12, 0);
}

static inline int hpt_get_pm_idx(VCPU *vcpu, u64 gpa, int lvl)
{

  int lo;
  int hi;

  ASSERT(lvl >= 1 && lvl <= 4);
  lo = (lvl-1)*9 + 12;
  hi = lo+8;

  return BR64_GET_HL(gpa, hi, lo);
}

#endif
