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

#include "unity.h"

#define __PRINT_H_ /* avoid indirectly including our print.h, which conflicts with libc stdio.h */

#define dprintf(...) while(0)

#include <inttypes.h>
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

#ifndef u32
typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
#endif

#include <hpt.h>


/* global CPU structs */
/* VCPU g_vcpubuffers[0]; */

void setUp(void)
{
}

void tearDown(void)
{
}

#define maxu64 0xffffffffffffffffull

void test_ZERO_HI64(void)
{
  TEST_ASSERT_EQUAL_HEX64(maxu64, ZERO_HI64(maxu64, 0));
  TEST_ASSERT_EQUAL_HEX64(0x7fffffffffffffffull, ZERO_HI64(maxu64, 1));
  TEST_ASSERT_EQUAL_HEX64(0x1ull, ZERO_HI64(maxu64, 63));
}

void test_ZERO_LO64(void)
{
  TEST_ASSERT_EQUAL_HEX64(maxu64, ZERO_LO64(maxu64, 0));
  TEST_ASSERT_EQUAL_HEX64(0xfffffffffffffffeull, ZERO_LO64(maxu64, 1));
  TEST_ASSERT_EQUAL_HEX64(0x8000000000000000ull, ZERO_LO64(maxu64, 63));
}

void test_MASKRANGE64(void)
{
  TEST_ASSERT_EQUAL_HEX64(0xffffffffffffffffull, MASKRANGE64(63, 0));
  TEST_ASSERT_EQUAL_HEX64(0x7fffffffffffffffull, MASKRANGE64(62, 0));
  TEST_ASSERT_EQUAL_HEX64(0x3ull, MASKRANGE64(1, 0));
  TEST_ASSERT_EQUAL_HEX64(0x1ull, MASKRANGE64(0, 0));

  TEST_ASSERT_EQUAL_HEX64(0x700ull, MASKRANGE64(10, 8));
  TEST_ASSERT_EQUAL_HEX64(0x8000000000000000ull, MASKRANGE64(63, 63));
}

void test_BR64_GET_HL(void)
{
  TEST_ASSERT_EQUAL_HEX64(0x1, BR64_GET_HL(maxu64, 0, 0));
  TEST_ASSERT_EQUAL_HEX64(0x1, BR64_GET_HL(maxu64, 1, 1));
  TEST_ASSERT_EQUAL_HEX64(0x1, BR64_GET_HL(maxu64, 63, 63));

  TEST_ASSERT_EQUAL_HEX64(0x3, BR64_GET_HL(maxu64, 1, 0));
  TEST_ASSERT_EQUAL_HEX64(0x3, BR64_GET_HL(maxu64, 63, 62));
  TEST_ASSERT_EQUAL_HEX64(0x3, BR64_GET_HL(maxu64, 32, 31));

  TEST_ASSERT_EQUAL_HEX64(maxu64, BR64_GET_HL(maxu64, 63, 0));
}

void test_BR64_SET_HL(void)
{
  TEST_ASSERT_EQUAL_HEX64(0x1, BR64_SET_HL(0, 0, 0, 1));
  TEST_ASSERT_EQUAL_HEX64(0x0, BR64_SET_HL(0, 0, 0, 0));
  TEST_ASSERT_EQUAL_HEX64(0x8000000000000000ull, BR64_SET_HL(0, 63, 63, 1));

  TEST_ASSERT_EQUAL_HEX64(0x700ull, BR64_SET_HL(0, 10, 8, 7));
}

void test_BR64_COPY_BITS_HL(void)
{
  TEST_ASSERT_EQUAL_HEX64(0, BR64_COPY_BITS_HL(0x0ull, 0x0ull, 0, 0, 0));
  TEST_ASSERT_EQUAL_HEX64(1, BR64_COPY_BITS_HL(0x0ull, 0x1ull, 0, 0, 0));
  TEST_ASSERT_EQUAL_HEX64(2, BR64_COPY_BITS_HL(0x0ull, 0x1ull, 0, 0, 1));

  TEST_ASSERT_EQUAL_HEX64(0x1, BR64_COPY_BITS_HL(0x0ull, 0x7ull, 0, 0, 0));
  TEST_ASSERT_EQUAL_HEX64(0x700, BR64_COPY_BITS_HL(0x0ull, 0x7ull, 2, 0, 8));
}

void test_BR64_GET_BIT(void)
{
  TEST_ASSERT_EQUAL_HEX64(0x0, BR64_GET_BIT(0xfffffffffffffffeull, 0));
  TEST_ASSERT_EQUAL_HEX64(0x0, BR64_GET_BIT(0x7fffffffffffffffull, 63));
}

void test_BR64_SET_BIT(void)
{
  TEST_ASSERT_EQUAL_HEX64(0x7fffffffffffffffull, BR64_SET_BIT(0xffffffffffffffffull, 63, 0));
  TEST_ASSERT_EQUAL_HEX64(0xffffffffffffffffull, BR64_SET_BIT(0x7fffffffffffffffull, 63, 1));
}

void test_hpt_setprot(void)
{
  
}

void test_hpt_getprot_intel(void)
{
  TEST_ASSERT_EQUAL_HEX64(0x0, hpt_pme_getprot(HPT_TYPE_EPT, 1, 0xfffffffffffffff8ull));

  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_R, hpt_pme_getprot(HPT_TYPE_EPT, 1, 0xfffffffffffffff9ull));
  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_W, hpt_pme_getprot(HPT_TYPE_EPT, 1, 0xfffffffffffffffaull));
  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_X, hpt_pme_getprot(HPT_TYPE_EPT, 1, 0xfffffffffffffffcull));

  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_RWX, hpt_pme_getprot(HPT_TYPE_EPT, 1, 0xffffffffffffffffull));
}

void test_hpt_getprot_amd(void)
{
  TEST_ASSERT_EQUAL_HEX64(0x0, hpt_pme_getprot(HPT_TYPE_LONG, 1, 0xfffffffffffffffcull));

  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_R, hpt_pme_getprot(HPT_TYPE_LONG, 1, 0xfffffffffffffffdull));
  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_W, hpt_pme_getprot(HPT_TYPE_LONG, 1, 0xfffffffffffffffeull));
  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_X, hpt_pme_getprot(HPT_TYPE_LONG, 1, 0x7ffffffffffffffcull));

  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_RWX, hpt_pme_getprot(HPT_TYPE_LONG, 1, 0x7fffffffffffffffull));
}

void test_hpt_setprot_amd(void)
{
  /* none to none */
  TEST_ASSERT_EQUAL_HEX64(0x8000000000000000ull,
                          hpt_pme_setprot(HPT_TYPE_LONG, 1, 0x0ull, HPT_PROTS_NONE));

  /* none to one */
  TEST_ASSERT_EQUAL_HEX64(0x8000000000000001ull,
                          hpt_pme_setprot(HPT_TYPE_LONG, 1, 0x0ull, HPT_PROTS_R));
  TEST_ASSERT_EQUAL_HEX64(0x8000000000000003ull,
                          hpt_pme_setprot(HPT_TYPE_LONG, 1, 0x0ull, HPT_PROTS_RW));
  TEST_ASSERT_EQUAL_HEX64(0x0000000000000001ull,
                          hpt_pme_setprot(HPT_TYPE_LONG, 1, 0x0ull, HPT_PROTS_RX));

  /* none to all */
  TEST_ASSERT_EQUAL_HEX64(0x0000000000000003ull,
                          hpt_pme_setprot(HPT_TYPE_LONG, 1, 0x0ull, HPT_PROTS_RWX));

  /* none to none */
  TEST_ASSERT_EQUAL_HEX64(0xfffffffffffffffcull,
                          hpt_pme_setprot(HPT_TYPE_LONG,
                                          1,
                                          0xfffffffffffffffcull,
                                          HPT_PROTS_NONE));

  /* none to one */
  TEST_ASSERT_EQUAL_HEX64(0xfffffffffffffffdull,
                          hpt_pme_setprot(HPT_TYPE_LONG,
                                          1,
                                          0xfffffffffffffffcull,
                                          HPT_PROTS_R));
  TEST_ASSERT_EQUAL_HEX64(0xffffffffffffffffull,
                          hpt_pme_setprot(HPT_TYPE_LONG,
                                          1,
                                          0xfffffffffffffffcull,
                                          HPT_PROTS_RW));
  TEST_ASSERT_EQUAL_HEX64(0x7ffffffffffffffdull,
                          hpt_pme_setprot(HPT_TYPE_LONG,
                                          1,
                                          0xfffffffffffffffcull,
                                          HPT_PROTS_RX));

  /* none to all */
  TEST_ASSERT_EQUAL_HEX64(0x7fffffffffffffffull,
                          hpt_pme_setprot(HPT_TYPE_LONG,
                                          1,
                                          0xfffffffffffffffcull,
                                          HPT_PROTS_RWX));

  /* all to none */
  TEST_ASSERT_EQUAL_HEX64(0xfffffffffffffffcull,
                          hpt_pme_setprot(HPT_TYPE_LONG,
                                          1,
                                          0x7ffffffffffffffcull,
                                          HPT_PROTS_NONE));

}

void test_hpt_getunused(void)
{
  TEST_ASSERT_EQUAL_HEX64(0x7, hpt_pme_getunused(HPT_TYPE_EPT, 1, 0x0000000000000e00ull, 2, 0));
  TEST_ASSERT_EQUAL_HEX64(0x7, hpt_pme_getunused(HPT_TYPE_EPT, 1, 0xffffffffffffffffull, 2, 0));

  TEST_ASSERT_EQUAL_HEX64(0x5, hpt_pme_getunused(HPT_TYPE_LONG, 1, 0x0000000000000a00ull, 2, 0));
  TEST_ASSERT_EQUAL_HEX64(0x5, hpt_pme_getunused(HPT_TYPE_LONG, 1, 0x0000000000000a00ull, 2, 0));
}

void test_pm_size(void)
{
  TEST_ASSERT_EQUAL_INT(4096, hpt_pm_size(HPT_TYPE_EPT, 1));
  TEST_ASSERT_EQUAL_INT(4096, hpt_pm_size(HPT_TYPE_EPT, 2));
  TEST_ASSERT_EQUAL_INT(4096, hpt_pm_size(HPT_TYPE_EPT, 3));
  TEST_ASSERT_EQUAL_INT(4096, hpt_pm_size(HPT_TYPE_EPT, 4));
}

void test_pme_get_address(void)
{
  TEST_ASSERT_EQUAL_HEX64(0x000ffffffffff000ull, hpt_pme_get_address(HPT_TYPE_EPT, 1, 0xffffffffffffffffull));
  TEST_ASSERT_EQUAL_HEX64(0x000ffffffffff000ull, hpt_pme_get_address(HPT_TYPE_EPT, 2, 0xffffffffffffffffull));
  TEST_ASSERT_EQUAL_HEX64(0x000ffffffffff000ull, hpt_pme_get_address(HPT_TYPE_EPT, 3, 0xffffffffffffffffull));
  TEST_ASSERT_EQUAL_HEX64(0x000ffffffffff000ull, hpt_pme_get_address(HPT_TYPE_EPT, 4, 0xffffffffffffffffull));

  TEST_ASSERT_EQUAL_HEX64(0x000ffffffffff000ull, hpt_pme_get_address(HPT_TYPE_EPT, 4, 0x000ffffffffff000ull));
  TEST_ASSERT_EQUAL_HEX64(0x000ffff0fffff000ull, hpt_pme_get_address(HPT_TYPE_EPT, 4, 0x000ffff0fffff000ull));
}

void test_pme_set_address(void)
{
  TEST_ASSERT_EQUAL_HEX64(0x000ffffffffff000ull, hpt_pme_set_address(HPT_TYPE_EPT, 1, 0x0ull, 0x000ffffffffff000ull));
  TEST_ASSERT_EQUAL_HEX64(0x000ffffffffff000ull, hpt_pme_set_address(HPT_TYPE_EPT, 1, 0x0ull, 0xffffffffffffffffull));
}

void test_get_pm_idx(void)
{
  TEST_ASSERT_EQUAL_HEX64(0x1ff, hpt_get_pm_idx(HPT_TYPE_EPT, 1, 0x1ffull<<12));
  TEST_ASSERT_EQUAL_HEX64(0x1ff, hpt_get_pm_idx(HPT_TYPE_EPT, 2, 0x1ffull<<12<<9));
  TEST_ASSERT_EQUAL_HEX64(0x1ff, hpt_get_pm_idx(HPT_TYPE_EPT, 3, 0x1ffull<<12<<9<<9));
  TEST_ASSERT_EQUAL_HEX64(0x1ff, hpt_get_pm_idx(HPT_TYPE_EPT, 4, 0x1ffull<<12<<9<<9<<9));
}

void test_get_pme_by_va(void)
{
  u64 pm[512] = { [0x100] = 0xdeadbeeff00dd00dull, [0x1ff] = 0xffffffffffffffffull };
  TEST_ASSERT_EQUAL_HEX64(0xffffffffffffffffull, hpt_pm_get_pme_by_va(HPT_TYPE_EPT, 1, pm, 0x1ffull<<12));
  TEST_ASSERT_EQUAL_HEX64(0xdeadbeeff00dd00dull, hpt_pm_get_pme_by_va(HPT_TYPE_EPT, 2, pm, 0x100ull<<12<<9));
}

void test_set_pme_by_va(void)
{
  u64 pm[512];
  hpt_pm_set_pme_by_va(HPT_TYPE_EPT, 2, pm, 0x50ull<<12<<9, 0xdeadbeeff00dd00dull);
  TEST_ASSERT_EQUAL_HEX64(pm[0x50], 0xdeadbeeff00dd00dull);
}

void test_cr3_set_address(void)
{
  TEST_ASSERT_EQUAL_HEX64(0xffffffe0,
                          hpt_cr3_set_address(HPT_TYPE_PAE, 0, 0xffffffff));
}
