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

#include <hpt.h>

/* page map sizes, in bytes. note that zero index is invalid. */
const u16 hpt_pm_sizes[HPT_TYPE_NUM][HPT_MAX_LEVEL+1] =
  {
    [HPT_TYPE_NORM] = {0, HPT_PM_SIZE, HPT_PM_SIZE, 0, 0},
    [HPT_TYPE_PAE]  = {0, HPT_PM_SIZE, HPT_PM_SIZE, 4*sizeof(hpt_pme_t), 0},
    [HPT_TYPE_LONG] = {0, HPT_PM_SIZE, HPT_PM_SIZE, HPT_PM_SIZE, HPT_PM_SIZE },
    [HPT_TYPE_EPT]  = {0, HPT_PM_SIZE, HPT_PM_SIZE, HPT_PM_SIZE, HPT_PM_SIZE },
  };

/* page map sizes, in bytes. note that zero index is invalid. */
const u16 hpt_pm_alignments[HPT_TYPE_NUM][HPT_MAX_LEVEL+1] =
  {
    [HPT_TYPE_NORM] = { 0, HPT_PM_SIZE, HPT_PM_SIZE, 0, 0},
    [HPT_TYPE_PAE]  = { 0, HPT_PM_SIZE, HPT_PM_SIZE, 32, 0},
    [HPT_TYPE_LONG] = { 0, HPT_PM_SIZE, HPT_PM_SIZE, HPT_PM_SIZE, 1 },
    [HPT_TYPE_EPT]  = { 0, HPT_PM_SIZE, HPT_PM_SIZE, HPT_PM_SIZE, HPT_PM_SIZE },
  };

/* high bit of va used to index into the page map of the given level.
 * we treat level '0' specially here, so that the low bit of the index
 * can consistently be found by looking up the entry for 'level-1'.
 */
const u8 hpt_va_idx_hi[HPT_TYPE_NUM][HPT_MAX_LEVEL+1] =
  {
    [HPT_TYPE_NORM] = { 11, 21, 31, 0, 0},
    [HPT_TYPE_PAE]  = { 11, 20, 29, 31, 0},
    [HPT_TYPE_LONG] = { 11, 20, 29, 38, 47},
    [HPT_TYPE_EPT]  = { 11, 20, 29, 38, 47},
  };

const u8 hpt_type_max_lvl[HPT_TYPE_NUM] =
  {
    [HPT_TYPE_NORM] = 2,
    [HPT_TYPE_PAE]  = 3,
    [HPT_TYPE_LONG] = 4,
    [HPT_TYPE_EPT]  = 4,
  };

size_t hpt_pm_size(hpt_type_t t, int lvl)
{
  size_t rv;
  assert(lvl <= HPT_MAX_LEVEL);
  rv = hpt_pm_sizes[t][lvl];
  assert(rv != 0);
  return rv;
}

u64 hpt_cr3_set_address(hpt_type_t t, u64 cr3, hpt_pa_t a)
{
  if (t==HPT_TYPE_NORM) {
    cr3 = BR64_COPY_BITS_HL(cr3, a, HPT_CR3_PML2_NORM_HI, HPT_CR3_PML2_NORM_LO, 0);
    cr3 = BR64_COPY_BITS_HL(cr3, 0, HPT_CR3_MBZ11_NORM_HI, HPT_CR3_MBZ11_NORM_LO, 0);
    cr3 = BR64_COPY_BITS_HL(cr3, 0, HPT_CR3_MBZ2_HI, HPT_CR3_MBZ2_LO, 0);
  } else if (t==HPT_TYPE_PAE) {
    cr3 = BR64_COPY_BITS_HL(cr3, a, HPT_CR3_PML3_PAE_HI, HPT_CR3_PML3_PAE_LO, 0);
    cr3 = BR64_COPY_BITS_HL(cr3, 0, HPT_CR3_MBZ2_HI, HPT_CR3_MBZ2_LO, 0);
  } else if (t==HPT_TYPE_LONG) {
    cr3 = BR64_COPY_BITS_HL(cr3, a, HPT_CR3_PML4_LONG_HI, HPT_CR3_PML4_LONG_LO, 0);
    cr3 = BR64_COPY_BITS_HL(cr3, 0, HPT_CR3_MBZ2_HI, HPT_CR3_MBZ2_LO, 0);
  } else if (t==HPT_TYPE_EPT) {
    assert(0); /* N\A. set EPTP ptr */
  } else {
    assert(0);
  }
  return cr3;
}

hpt_pa_t hpt_cr3_get_address(hpt_type_t t, u64 cr3)
{
  if (t==HPT_TYPE_NORM) {
    return BR64_COPY_BITS_HL(0, cr3, HPT_CR3_PML2_NORM_HI, HPT_CR3_PML2_NORM_LO, 0);
  } else if (t==HPT_TYPE_PAE) {
    return BR64_COPY_BITS_HL(0, cr3, HPT_CR3_PML3_PAE_HI, HPT_CR3_PML3_PAE_LO, 0);
  } else if (t==HPT_TYPE_LONG) {
    return BR64_COPY_BITS_HL(0, cr3, HPT_CR3_PML4_LONG_HI, HPT_CR3_PML4_LONG_LO, 0);
  } else if (t==HPT_TYPE_EPT) {
    assert(0); /* N\A. set EPTP ptr */
  } else {
    assert(0);
  }
  assert(0); return (hpt_pa_t)0; /* unreachable; appeases compiler */
}

u64 hpt_eptp_set_address(hpt_type_t t, u64 eptp, hpt_pa_t a)
{
  assert(t == HPT_TYPE_EPT);
  return BR64_COPY_BITS_HL(eptp, a, HPT_EPTP_PML4_HI, HPT_EPTP_PML4_LO, 0);
}

hpt_pa_t hpt_eptp_get_address(hpt_type_t t, u64 eptp)
{
  assert(t == HPT_TYPE_EPT);
  return BR64_COPY_BITS_HL(0, eptp, HPT_EPTP_PML4_HI, HPT_EPTP_PML4_LO, 0);
}
