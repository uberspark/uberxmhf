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

#include "unity.h"

#define __PRINT_H_ /* avoid indirectly including our print.h, which conflicts with libc stdio.h */
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

void test_ZERO_HI(void)
{
  TEST_ASSERT_EQUAL_HEX64(maxu64, ZERO_HI(maxu64, 0));
  TEST_ASSERT_EQUAL_HEX64(0x7fffffffffffffffull, ZERO_HI(maxu64, 1));
  TEST_ASSERT_EQUAL_HEX64(0x1ull, ZERO_HI(maxu64, 63));
}

void test_ZERO_LO(void)
{
  TEST_ASSERT_EQUAL_HEX64(maxu64, ZERO_LO(maxu64, 0));
  TEST_ASSERT_EQUAL_HEX64(0xfffffffffffffffeull, ZERO_LO(maxu64, 1));
  TEST_ASSERT_EQUAL_HEX64(0x8000000000000000ull, ZERO_LO(maxu64, 63));
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
  TEST_ASSERT_EQUAL_HEX64(0x0, hpt_getprot(PT_TYPE_EPT, 0xfffffffffffffff8ull));

  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_R, hpt_getprot(PT_TYPE_EPT, 0xfffffffffffffff9ull));
  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_W, hpt_getprot(PT_TYPE_EPT, 0xfffffffffffffffaull));
  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_X, hpt_getprot(PT_TYPE_EPT, 0xfffffffffffffffcull));

  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_RWX, hpt_getprot(PT_TYPE_EPT, 0xffffffffffffffffull));
}

void test_hpt_getprot_amd(void)
{
  TEST_ASSERT_EQUAL_HEX64(0x0, hpt_getprot(PT_TYPE_LONG, 0xfffffffffffffffcull));

  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_R, hpt_getprot(PT_TYPE_LONG, 0xfffffffffffffffdull));
  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_W, hpt_getprot(PT_TYPE_LONG, 0xfffffffffffffffeull));
  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_X, hpt_getprot(PT_TYPE_LONG, 0x7ffffffffffffffcull));

  TEST_ASSERT_EQUAL_HEX64(HPT_PROTS_RWX, hpt_getprot(PT_TYPE_LONG, 0x7fffffffffffffffull));
}

void test_hpt_setprot_amd(void)
{
  /* none to none */
  TEST_ASSERT_EQUAL_HEX64(0x8000000000000000ull,
                          hpt_setprot(PT_TYPE_LONG, 0x0ull, HPT_PROTS_NONE));

  /* none to one */
  TEST_ASSERT_EQUAL_HEX64(0x8000000000000001ull,
                          hpt_setprot(PT_TYPE_LONG, 0x0ull, HPT_PROTS_R));
  TEST_ASSERT_EQUAL_HEX64(0x8000000000000002ull,
                          hpt_setprot(PT_TYPE_LONG, 0x0ull, HPT_PROTS_W));
  TEST_ASSERT_EQUAL_HEX64(0x0000000000000000ull,
                          hpt_setprot(PT_TYPE_LONG, 0x0ull, HPT_PROTS_X));

  /* none to all */
  TEST_ASSERT_EQUAL_HEX64(0x0000000000000003ull,
                          hpt_setprot(PT_TYPE_LONG, 0x0ull, HPT_PROTS_RWX));

  /* none to none */
  TEST_ASSERT_EQUAL_HEX64(0xfffffffffffffffcull,
                          hpt_setprot(PT_TYPE_LONG,
                                      0xfffffffffffffffcull,
                                      HPT_PROTS_NONE));

  /* none to one */
  TEST_ASSERT_EQUAL_HEX64(0xfffffffffffffffdull,
                          hpt_setprot(PT_TYPE_LONG,
                                      0xfffffffffffffffcull,
                                      HPT_PROTS_R));
  TEST_ASSERT_EQUAL_HEX64(0xfffffffffffffffeull,
                          hpt_setprot(PT_TYPE_LONG,
                                      0xfffffffffffffffcull,
                                      HPT_PROTS_W));
  TEST_ASSERT_EQUAL_HEX64(0x7ffffffffffffffcull,
                          hpt_setprot(PT_TYPE_LONG,
                                      0xfffffffffffffffcull,
                                      HPT_PROTS_X));

  /* none to all */
  TEST_ASSERT_EQUAL_HEX64(0x7fffffffffffffffull,
                          hpt_setprot(PT_TYPE_LONG,
                                      0xfffffffffffffffcull,
                                      HPT_PROTS_RWX));

  /* all to none */
  TEST_ASSERT_EQUAL_HEX64(0xfffffffffffffffcull,
                          hpt_setprot(PT_TYPE_LONG,
                                      0x7ffffffffffffffcull,
                                      HPT_PROTS_NONE));

}

void test_hpt_getunused(void)
{
  TEST_ASSERT_EQUAL_HEX64(0x7, hpt_getunused(PT_TYPE_EPT, 0x0000000000000e00ull, 2, 0));
  TEST_ASSERT_EQUAL_HEX64(0x7, hpt_getunused(PT_TYPE_EPT, 0xffffffffffffffffull, 2, 0));

  TEST_ASSERT_EQUAL_HEX64(0x5, hpt_getunused(PT_TYPE_LONG, 0x0000000000000a00ull, 2, 0));
  TEST_ASSERT_EQUAL_HEX64(0x5, hpt_getunused(PT_TYPE_LONG, 0x0000000000000a00ull, 2, 0));
}
