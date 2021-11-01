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

#include <hpt.h>
#include "hpt_internal.h"

hpt_pme_t hpt_pme_setuser(hpt_type_t t, int lvl, hpt_pme_t entry, bool user_accessible)
{
  if (t == HPT_TYPE_NORM) {
    return BR64_SET_BIT(entry, HPT_NORM_US_L21_MP_BIT, user_accessible);
  } else if (t == HPT_TYPE_PAE) {
    if (lvl == 3) {
      assert(user_accessible);
      return entry;
    } else {
      return BR64_SET_BIT(entry, HPT_PAE_US_L21_MP_BIT, user_accessible);
    }
  } else if (t == HPT_TYPE_LONG) {
    return BR64_SET_BIT(entry, HPT_LONG_US_L4321_MP_BIT, user_accessible);
  } else if (t == HPT_TYPE_EPT) {
    assert(user_accessible);
    return entry;
  }
  assert(0); return 0; /* unreachable; appeases compiler */
}

bool hpt_pme_getuser(hpt_type_t t, int lvl, hpt_pme_t entry)
{
  if (t == HPT_TYPE_NORM) {
    return BR64_GET_BIT(entry, HPT_NORM_US_L21_MP_BIT);
  } else if (t == HPT_TYPE_PAE) {
    if (lvl == 3) {
      return true;
    } else {
      return BR64_GET_BIT(entry, HPT_PAE_US_L21_MP_BIT);
    }
  } else if (t == HPT_TYPE_LONG) {
    return BR64_GET_BIT(entry, HPT_LONG_US_L4321_MP_BIT);
  } else if (t == HPT_TYPE_EPT) {
    return true;
  }
  assert(0); return false; /* unreachable; appeases compiler */
}

hpt_pme_t hpt_pme_setprot(hpt_type_t t, int lvl, hpt_pme_t entry, hpt_prot_t perms)
{
  hpt_pme_t rv=entry;
  assert(hpt_lvl_is_valid(t, lvl));
  assert(hpt_prot_is_valid(t, lvl, perms));

  if (t == HPT_TYPE_NORM) {
    rv = BR64_SET_BIT(rv, HPT_NORM_P_L21_MP_BIT, perms & HPT_PROT_READ_MASK);
    rv = BR64_SET_BIT(rv, HPT_NORM_RW_L21_MP_BIT, perms & HPT_PROT_WRITE_MASK);
  } else if (t == HPT_TYPE_PAE) {
    rv = BR64_SET_BIT(rv, HPT_PAE_P_L321_MP_BIT, perms & HPT_PROT_READ_MASK);
    if (lvl == 2 || lvl == 1) {
      rv = BR64_SET_BIT(rv, HPT_PAE_RW_L21_MP_BIT, perms & HPT_PROT_WRITE_MASK);
      rv = BR64_SET_BIT(rv, HPT_PAE_NX_L21_MP_BIT, !(perms & HPT_PROT_EXEC_MASK));
    }
  } else if (t == HPT_TYPE_LONG) {
    rv = BR64_SET_BIT(rv, HPT_LONG_P_L4321_MP_BIT, perms & HPT_PROT_READ_MASK);
    rv = BR64_SET_BIT(rv, HPT_LONG_RW_L4321_MP_BIT, perms & HPT_PROT_WRITE_MASK);
    rv = BR64_SET_BIT(rv, HPT_LONG_NX_L4321_MP_BIT, !(perms & HPT_PROT_EXEC_MASK));
  } else if (t == HPT_TYPE_EPT) {
    rv = BR64_SET_BR(rv, HPT_EPT_PROT_L4321_MP, perms);
  } else {
    assert(0);
  }

  return rv;
}

hpt_prot_t hpt_pme_getprot(hpt_type_t t, int lvl, hpt_pme_t entry)
{
  hpt_prot_t rv=HPT_PROTS_NONE;
  bool r,w,x;
  assert(hpt_lvl_is_valid(t, lvl));

  if (t == HPT_TYPE_NORM) {
    r= entry & MASKBIT64(HPT_NORM_P_L21_MP_BIT);
    w= entry & MASKBIT64(HPT_NORM_RW_L21_MP_BIT);
    x= r;
  } else if (t == HPT_TYPE_PAE) {
    r= entry & MASKBIT64(HPT_PAE_P_L321_MP_BIT);
    if (lvl == 2 || lvl == 1) {
      w= entry & MASKBIT64(HPT_PAE_RW_L21_MP_BIT);
      x= !(entry & MASKBIT64(HPT_PAE_NX_L21_MP_BIT));;
    } else {
      w=r;
      x=r;
    }
  } else if (t == HPT_TYPE_LONG) {
    r=entry & MASKBIT64(HPT_LONG_P_L4321_MP_BIT);
    w=entry & MASKBIT64(HPT_LONG_RW_L4321_MP_BIT);
    x=!(entry & MASKBIT64(HPT_LONG_NX_L4321_MP_BIT));
  } else if (t == HPT_TYPE_EPT) {
    r=entry & MASKBIT64(HPT_EPT_R_L4321_MP_BIT);
    w=entry & MASKBIT64(HPT_EPT_W_L4321_MP_BIT);
    x=entry & MASKBIT64(HPT_EPT_X_L4321_MP_BIT);
  } else {
    assert(0);
  }
  rv = HPT_PROTS_NONE;
  rv = rv | (r ? HPT_PROT_READ_MASK : 0);
  rv = rv | (w ? HPT_PROT_WRITE_MASK : 0);
  rv = rv | (x ? HPT_PROT_EXEC_MASK : 0);

  return rv;
}

hpt_pme_t hpt_pme_setunused(hpt_type_t t, int lvl, hpt_pme_t entry, int hi, int lo, hpt_pme_t val)
{
  hpt_pme_t rv=entry;
  assert(hi>lo);
  HPT_UNUSED_ARGUMENT(lvl);

  /* bits 9, 10, and 11 are unused in all levels of all current page
     types. For convenience and simplicity we map those to\from bits 2-0.

     If we need more unused bits, for some page table types and levels other
     bits are available. 
  */
     
  if(t == HPT_TYPE_NORM
     || t == HPT_TYPE_PAE
     || t == HPT_TYPE_LONG
     || t == HPT_TYPE_EPT) {
    assert(hi <= 2); /* we can remove this limitation for some table
                        types and levels if necessary. */
    rv = BR64_COPY_BITS_HL(rv, val, MIN(2,hi), MAX(0,lo), (9-0));
  } else {
    assert(0);
  }
  return rv;
}

hpt_pme_t hpt_pme_getunused(hpt_type_t t, int lvl, hpt_pme_t entry, int hi, int lo)
{
  hpt_pme_t rv = 0ull;
  assert(hi>lo);
  HPT_UNUSED_ARGUMENT(lvl);

  if(t == HPT_TYPE_NORM
     || t == HPT_TYPE_PAE
     || t == HPT_TYPE_LONG
     || t == HPT_TYPE_EPT) {
    assert(hi <= 2); /* we can remove this limitation for some table
                        types and levels if necessary. */
    rv = BR64_COPY_BITS_HL(rv, entry, MIN(2,hi), MAX(0,lo), (9-0));
    rv = BR64_GET_HL(entry, MIN(2,hi)+9, MAX(0,lo)+9);
  } else {
    assert(0);
  }
  return rv;
}

bool hpt_pme_is_present(hpt_type_t t, int lvl, hpt_pme_t entry)
{
  /* a valid entry is present iff read access is enabled. */
  return hpt_pme_getprot(t, lvl, entry) & HPT_PROT_READ_MASK;
}

bool hpt_pme_is_page(hpt_type_t t, int lvl, hpt_pme_t entry)
{
  if (t== HPT_TYPE_NORM) {
    assert(lvl<=2);
    return lvl == 1 || (lvl==2 && BR64_GET_BIT(entry, HPT_NORM_PS_L2_MP_BIT));
  } else if (t == HPT_TYPE_PAE) {
    assert(lvl<=3);
    return lvl == 1 || (lvl==2 && BR64_GET_BIT(entry, HPT_PAE_PS_L2_MP_BIT));
  } else if (t == HPT_TYPE_LONG) {
    assert(lvl<=3);
    return lvl == 1 || ((lvl==2 || lvl==3) && BR64_GET_BIT(entry, HPT_LONG_PS_L32_MP_BIT));
  } else if (t == HPT_TYPE_EPT) {
    assert(lvl<=4);
    return lvl == 1 || ((lvl==2 || lvl==3) && BR64_GET_BIT(entry, HPT_EPT_PS_L32_MP_BIT));
  } else {
    assert(0);
    return false;
  }
}

hpt_pa_t hpt_pme_get_address(hpt_type_t t, int lvl, hpt_pme_t entry)
{
  if (t == HPT_TYPE_NORM) {
    assert(lvl<=2);
    if(lvl==2) {
      if (hpt_pme_is_page(t,lvl,entry)) {
        /* 4 MB page */
        hpt_pa_t rv = 0;
        rv = BR64_COPY_BITS_HL(rv, entry,
                               39, 32,
                               32-HPT_NORM_ADDR3932_L2_P_LO);
        rv = BR64_COPY_BITS_HL(rv, entry,
                               31, 22,
                               22-HPT_NORM_ADDR3122_L2_P_LO);
        return rv;
      } else {
        return BR64_COPY_BITS_HL(0, entry,
                                 HPT_NORM_ADDR_L2_M_HI,
                                 HPT_NORM_ADDR_L2_M_LO, 0);
      }
    } else {
      return BR64_COPY_BITS_HL(0, entry,
                               HPT_NORM_ADDR_L1_P_HI,
                               HPT_NORM_ADDR_L1_P_LO, 0);
    }
  } else if (t == HPT_TYPE_PAE) {
    assert(lvl<=3);
    if (hpt_pme_is_page(t, lvl, entry)) {
      if (lvl == 1) {
        return BR64_COPY_BITS_HL(0, entry,
                                 HPT_PAE_ADDR_L1_P_HI,
                                 HPT_PAE_ADDR_L1_P_LO, 0);
      } else {
        assert(lvl==2);
        return BR64_COPY_BITS_HL(0, entry,
                                 HPT_PAE_ADDR_L2_P_HI,
                                 HPT_PAE_ADDR_L2_P_LO, 0);
      }
    } else {
      return BR64_COPY_BITS_HL(0, entry,
                               HPT_PAE_ADDR_L321_M_HI,
                               HPT_PAE_ADDR_L321_M_LO, 0);
    }
  } else if (t == HPT_TYPE_LONG) {
    assert(lvl<=4);
    if (hpt_pme_is_page(t, lvl, entry)) {
      if(lvl==1) {
        return BR64_COPY_BITS_HL(0, entry,
                                 HPT_LONG_ADDR_L1_P_HI,
                                 HPT_LONG_ADDR_L1_P_LO, 0);
      } else {
        return BR64_COPY_BITS_HL(0, entry,
                                 HPT_LONG_ADDR_L32_P_HI,
                                 HPT_LONG_ADDR_L32_P_LO, 0);
      }
    } else {
      return BR64_COPY_BITS_HL(0, entry,
                               HPT_LONG_ADDR_L4321_M_HI,
                               HPT_LONG_ADDR_L4321_M_LO, 0);
    }
  } else if (t == HPT_TYPE_EPT) {
    assert(lvl<=4);
    return BR64_COPY_BITS_HL(0, entry,
                             HPT_EPT_ADDR_L4321_MP_HI,
                             HPT_EPT_ADDR_L4321_MP_LO, 0);
  } else {
    assert(0);
    return 0;
  }
}

hpt_pme_t hpt_pme_set_address(hpt_type_t t, int lvl, hpt_pme_t entry, hpt_pa_t addr)
{
  if (t == HPT_TYPE_NORM) {
    assert(lvl<=2);
    if(lvl==2) {
      if (hpt_pme_is_page(t,lvl,entry)) {
        hpt_pme_t rv = entry;
        /* 4 MB page */
        rv = BR64_COPY_BITS_HL(entry, addr,
                               HPT_NORM_ADDR3932_L2_P_HI,
                               HPT_NORM_ADDR3932_L2_P_LO,
                               HPT_NORM_ADDR3932_L2_P_LO-32);
        rv = BR64_COPY_BITS_HL(entry, addr,
                               HPT_NORM_ADDR3122_L2_P_HI,
                               HPT_NORM_ADDR3122_L2_P_LO,
                               HPT_NORM_ADDR3122_L2_P_LO-22);
        return rv;
      } else {
        return BR64_COPY_BITS_HL(entry, addr,
                                 HPT_NORM_ADDR_L2_M_HI,
                                 HPT_NORM_ADDR_L2_M_LO, 0);
      }
    } else {
      return BR64_COPY_BITS_HL(entry, addr,
                               HPT_NORM_ADDR_L1_P_HI,
                               HPT_NORM_ADDR_L1_P_LO, 0);
    }
  } else if (t == HPT_TYPE_PAE) {
    assert(lvl<=3);
    if (hpt_pme_is_page(t, lvl, entry)) {
      if (lvl == 1) {
        return BR64_COPY_BITS_HL(entry, addr,
                                 HPT_PAE_ADDR_L1_P_HI,
                                 HPT_PAE_ADDR_L1_P_LO, 0);
      } else {
        assert(lvl==2);
        return BR64_COPY_BITS_HL(entry, addr,
                                 HPT_PAE_ADDR_L2_P_HI,
                                 HPT_PAE_ADDR_L2_P_LO, 0);
      }
    } else {
      return BR64_COPY_BITS_HL(entry, addr,
                               HPT_PAE_ADDR_L321_M_HI,
                               HPT_PAE_ADDR_L321_M_LO, 0);
    }
  } else if (t == HPT_TYPE_LONG) {
    assert(lvl<=4);
    if (hpt_pme_is_page(t, lvl, entry)) {
      if(lvl==1) {
        return BR64_COPY_BITS_HL(entry, addr,
                                 HPT_LONG_ADDR_L1_P_HI,
                                 HPT_LONG_ADDR_L1_P_LO, 0);
      } else {
        return BR64_COPY_BITS_HL(entry, addr,
                                 HPT_LONG_ADDR_L32_P_HI,
                                 HPT_LONG_ADDR_L32_P_LO, 0);
      }
    } else {
      return BR64_COPY_BITS_HL(entry, addr,
                               HPT_LONG_ADDR_L4321_M_HI,
                               HPT_LONG_ADDR_L4321_M_LO, 0);
    }
  } else if (t == HPT_TYPE_EPT) {
    assert(lvl<=4);
    return BR64_COPY_BITS_HL(entry, addr,
                             HPT_EPT_ADDR_L4321_MP_HI,
                             HPT_EPT_ADDR_L4321_MP_LO, 0);
  } else {
    assert(0);
    return 0;
  }
}

/* "internal". use hpt_pme_set_pmt instead */
static hpt_pme_t hpt_pme_set_pat(hpt_type_t t, int lvl, hpt_pme_t pme, bool pat)
{
  hpt_pme_t rv;
  if (t == HPT_TYPE_NORM) {
    rv = pme;
    if (hpt_pme_is_page(t, lvl, pme) && lvl==1) {
      rv = BR64_SET_BIT(rv, HPT_NORM_PAT_L1_P_BIT, pat);
    } else if (hpt_pme_is_page(t, lvl, pme) && lvl==2) {
      rv = BR64_SET_BIT(rv, HPT_NORM_PAT_L2_P_BIT, pat);
    } else {
      assert(!pat);
    }
  } else if (t== HPT_TYPE_PAE) {
    rv = pme;
    if (hpt_pme_is_page(t, lvl, pme) && lvl==1) {
      rv = BR64_SET_BIT(rv, HPT_PAE_PAT_L1_P_BIT, pat);
    } else if (hpt_pme_is_page(t, lvl, pme) && lvl==2) {
      rv = BR64_SET_BIT(rv, HPT_PAE_PAT_L2_P_BIT, pat);
    } else {
      assert(!pat);
    }
  } else if (t==HPT_TYPE_LONG) {
    rv = pme;
    if (hpt_pme_is_page(t, lvl, pme) && lvl==1) {
      rv = BR64_SET_BIT(rv, HPT_LONG_PAT_L1_P_BIT, pat);
    } else if (hpt_pme_is_page(t, lvl, pme) && (lvl==2||lvl==3)) {
      rv = BR64_SET_BIT(rv, HPT_LONG_PAT_L32_P_BIT, pat);
    } else {
      assert(!pat);
    }
  } else {
    assert(0);
  }
  return rv;
}

/* "internal". use hpt_pme_get_pmt instead */
static bool hpt_pme_get_pat(hpt_type_t t, int lvl, hpt_pme_t pme) __attribute__((unused));

static bool hpt_pme_get_pat(hpt_type_t t, int lvl, hpt_pme_t pme)
{
  if (t == HPT_TYPE_NORM) {
    if (hpt_pme_is_page(t, lvl, pme) && lvl==1) {
      return BR64_GET_BIT(pme, HPT_NORM_PAT_L1_P_BIT);
    } else if (hpt_pme_is_page(t, lvl, pme) && lvl==2) {
      return BR64_GET_BIT(pme, HPT_NORM_PAT_L2_P_BIT);
    } else {
      return false;
    }
  } else if (t== HPT_TYPE_PAE) {
    if (hpt_pme_is_page(t, lvl, pme) && lvl==1) {
      return BR64_GET_BIT(pme, HPT_PAE_PAT_L1_P_BIT);
    } else if (hpt_pme_is_page(t, lvl, pme) && lvl==2) {
      return BR64_GET_BIT(pme, HPT_PAE_PAT_L2_P_BIT);
    } else {
      return false;
    }
  } else if (t==HPT_TYPE_LONG) {
    if (hpt_pme_is_page(t, lvl, pme) && lvl==1) {
      return BR64_GET_BIT(pme, HPT_LONG_PAT_L1_P_BIT);
    } else if (hpt_pme_is_page(t, lvl, pme) && (lvl==2||lvl==3)) {
      return BR64_GET_BIT(pme, HPT_LONG_PAT_L32_P_BIT);
    } else {
      return false;
    }
  } else {
    assert(0);
  }
  return pme;
}

/* "internal". use hpt_pme_get_pmt instead */
static bool hpt_pme_get_pcd(hpt_type_t t, int __attribute__((unused)) lvl, hpt_pme_t pme)
{
  if (t == HPT_TYPE_NORM) {
    return BR64_GET_BIT(pme, HPT_NORM_PCD_L21_MP_BIT);
  } else if (t== HPT_TYPE_PAE) {
    return BR64_GET_BIT(pme, HPT_PAE_PCD_L321_MP_BIT);
  } else if (t==HPT_TYPE_LONG) {
    return  BR64_GET_BIT(pme, HPT_LONG_PCD_L4321_MP_BIT);
  } else {
    assert(0);
  }
  assert(0); return false; /* unreachable; appeases compiler */  
}

/* "internal". use hpt_pme_set_pmt instead */
static hpt_pme_t hpt_pme_set_pcd(hpt_type_t t, int __attribute__((unused)) lvl, hpt_pme_t pme, bool pcd)
{
  if (t == HPT_TYPE_NORM) {
    return BR64_SET_BIT(pme, HPT_NORM_PCD_L21_MP_BIT, pcd);
  } else if (t== HPT_TYPE_PAE) {
    return BR64_SET_BIT(pme, HPT_PAE_PCD_L321_MP_BIT, pcd);
  } else if (t==HPT_TYPE_LONG) {
    return  BR64_SET_BIT(pme, HPT_LONG_PCD_L4321_MP_BIT, pcd);
  } else {
    assert(0);
  }
  assert(0); return (hpt_pme_t)0; /* unreachable; appeases compiler */  
}

/* "internal". use hpt_pme_get_pmt instead */
static bool hpt_pme_get_pwt(hpt_type_t t, int __attribute__((unused)) lvl, hpt_pme_t pme)
{
  if (t == HPT_TYPE_NORM) {
    return BR64_GET_BIT(pme, HPT_NORM_PWT_L21_MP_BIT);
  } else if (t== HPT_TYPE_PAE) {
    return BR64_GET_BIT(pme, HPT_PAE_PWT_L321_MP_BIT);
  } else if (t==HPT_TYPE_LONG) {
    return  BR64_GET_BIT(pme, HPT_LONG_PWT_L4321_MP_BIT);
  } else {
    assert(0);
  }
  assert(0); return false; /* unreachable; appeases compiler */  
}

/* "internal". use hpt_pme_set_pmt instead */
static hpt_pme_t hpt_pme_set_pwt(hpt_type_t t, int __attribute__((unused)) lvl, hpt_pme_t pme, bool pwt)
{
  if (t == HPT_TYPE_NORM) {
    return BR64_SET_BIT(pme, HPT_NORM_PWT_L21_MP_BIT, pwt);
  } else if (t== HPT_TYPE_PAE) {
    return BR64_SET_BIT(pme, HPT_PAE_PWT_L321_MP_BIT, pwt);
  } else if (t==HPT_TYPE_LONG) {
    return  BR64_SET_BIT(pme, HPT_LONG_PWT_L4321_MP_BIT, pwt);
  } else {
    assert(0);
  }
  assert(0); return (hpt_pme_t)0; /* unreachable; appeases compiler */  
}

/* Assumes PAT register has default values */
hpt_pmt_t hpt_pme_get_pmt(hpt_type_t t, int lvl, hpt_pme_t pme)
{
  hpt_pmt_t rv;
  if (t == HPT_TYPE_EPT) {
    assert(lvl <= 3 && hpt_pme_is_page(t, lvl, pme));
    rv = BR64_GET_HL(pme, HPT_EPT_MT_L321_P_HI, HPT_EPT_MT_L321_P_LO);
  } else if (t == HPT_TYPE_PAE || t == HPT_TYPE_LONG || t == HPT_TYPE_NORM) {
    bool pcd, pwt;
    pcd = hpt_pme_get_pcd(t, lvl, pme);
    pwt = hpt_pme_get_pwt(t, lvl, pme);
    if (!pcd && !pwt) {
      return HPT_PMT_WB;
    } else if (!pcd && pwt) {
      return HPT_PMT_WT;
    } else if (pcd && !pwt) {
      return HPT_PMT_WC; /* really UC- unless overriden by mtrr */
    } else if (pcd && pwt) {
      return HPT_PMT_UC;
    }
  } else {
    assert(0);
  }
  return rv;
}

/* Always clears PAT bit when applicable. */
hpt_pmt_t hpt_pme_set_pmt(hpt_type_t t, int lvl, hpt_pme_t pme, hpt_pmt_t pmt)
{
  hpt_pme_t rv;
  if (t == HPT_TYPE_EPT) {
    assert(lvl <= 3 && hpt_pme_is_page(t, lvl, pme));
    rv = BR64_SET_HL(pme, HPT_EPT_MT_L321_P_HI, HPT_EPT_MT_L321_P_LO, pmt);
  } else if (t == HPT_TYPE_NORM || t == HPT_TYPE_PAE || t == HPT_TYPE_LONG) {
    bool pat, pcd, pwt;
    pat=0;
    if (pmt == HPT_PMT_UC) {
      pcd=1;
      pwt=1;
    } else if (pmt == HPT_PMT_WC) {
      pcd=1;
      pwt=0; /* this is actually 'UC-'. can be overriden to WC by setting MTRR */
    } else if (pmt == HPT_PMT_WT) {
      pcd=0;
      pwt=1;
    } else if (pmt == HPT_PMT_WP) {
      assert(0); /* can only get this by manipulating PAT register */
    } else if (pmt == HPT_PMT_WB) {
      pcd=0;
      pwt=0;
    } else {
      assert(0);
    }
    rv = pme;
    rv = hpt_pme_set_pat(t, lvl, rv, pat);
    rv = hpt_pme_set_pcd(t, lvl, rv, pcd);
    rv = hpt_pme_set_pwt(t, lvl, rv, pwt);
  } else {
    assert(0);
  }
  return rv;
}

unsigned int hpt_get_pm_idx(hpt_type_t t, int lvl, hpt_va_t va)
{
  unsigned int lo;
  unsigned int hi;
  assert(hpt_type_is_valid(t));
  assert(hpt_lvl_is_valid(t, lvl));

  hi = hpt_va_idx_hi[t][lvl];
  lo = hpt_va_idx_hi[t][lvl-1]+1;

  return BR64_GET_HL(va, hi, lo);
}

hpt_pme_t hpt_pm_get_pme_by_idx(hpt_type_t t, int lvl, hpt_pm_t pm, int idx)
{
  HPT_UNUSED_ARGUMENT(lvl);
  if(t == HPT_TYPE_EPT || t == HPT_TYPE_PAE || t == HPT_TYPE_LONG) {
    return ((u64*)pm)[idx];
  } else if (t == HPT_TYPE_NORM) {
    return ((u32*)pm)[idx];
  } else {
    assert(0);
    return 0;
  }
}

void hpt_pm_set_pme_by_idx(hpt_type_t t, int lvl, hpt_pm_t pm, int idx, hpt_pme_t pme)
{
  HPT_UNUSED_ARGUMENT(lvl);
  if(t == HPT_TYPE_EPT || t == HPT_TYPE_PAE || t == HPT_TYPE_LONG) {
    ((u64*)pm)[idx] = pme;
  } else if (t == HPT_TYPE_NORM) {
    ((u32*)pm)[idx] = pme;
  } else {
    assert(0);
  }
}

hpt_pme_t hpt_pm_get_pme_by_va(hpt_type_t t, int lvl, hpt_pm_t pm, hpt_va_t va)
{
  return hpt_pm_get_pme_by_idx(t, lvl, pm, hpt_get_pm_idx(t, lvl, va));
}

void hpt_pm_set_pme_by_va(hpt_type_t t, int lvl, hpt_pm_t pm, hpt_va_t va, hpt_pme_t pme)
{
  hpt_pm_set_pme_by_idx(t, lvl, pm, hpt_get_pm_idx(t, lvl, va), pme);
}
