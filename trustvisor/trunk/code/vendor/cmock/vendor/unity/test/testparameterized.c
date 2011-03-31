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

/* ==========================================
    Unity Project - A Test Framework for C
    Copyright (c) 2007 Mike Karlesky, Mark VanderVoord, Greg Williams
    [Released under MIT License. Please refer to license.txt for details]
========================================== */

#include <setjmp.h>
#include "unity.h"

#define EXPECT_ABORT_BEGIN \
    if (TEST_PROTECT())    \
    {
    
#define VERIFY_FAILS_END                                                       \
    }                                                                          \
    Unity.CurrentTestFailed = (Unity.CurrentTestFailed == 1) ? 0 : 1;          \
    if (Unity.CurrentTestFailed == 1) {                                        \
      SetToOneMeanWeAlreadyCheckedThisGuy = 1;                                 \
      UnityPrint("[[[[ Previous Test Should Have Failed But Did Not ]]]]");    \
      UNITY_OUTPUT_CHAR('\n');                                                 \
    }
    
#define VERIFY_IGNORES_END                                                     \
    }                                                                          \
    Unity.CurrentTestFailed = (Unity.CurrentTestIgnored == 1) ? 0 : 1;         \
    Unity.CurrentTestIgnored = 0;                                              \
    if (Unity.CurrentTestFailed == 1) {                                        \
      SetToOneMeanWeAlreadyCheckedThisGuy = 1;                                 \
      UnityPrint("[[[[ Previous Test Should Have Ignored But Did Not ]]]]");   \
      UNITY_OUTPUT_CHAR('\n');                                                 \
    }

int SetToOneToFailInTearDown;
int SetToOneMeanWeAlreadyCheckedThisGuy;

void setUp(void)
{
  SetToOneToFailInTearDown = 0;
  SetToOneMeanWeAlreadyCheckedThisGuy = 0;
}

void tearDown(void)
{
  if (SetToOneToFailInTearDown == 1)
    TEST_FAIL_MESSAGE("<= Failed in tearDown");
  if ((SetToOneMeanWeAlreadyCheckedThisGuy == 0) && (Unity.CurrentTestFailed > 0))
  {
    UnityPrint("[[[[ Previous Test Should Have Passed But Did Not ]]]]");
    UNITY_OUTPUT_CHAR('\n');
  }
}

TEST_CASE(0)
TEST_CASE(44)
TEST_CASE(99)
void test_TheseShouldAllPass(int Num)
{
    TEST_ASSERT_TRUE(Num < 100);
}

TEST_CASE(3)
TEST_CASE(77)
TEST_CASE(99)
void test_TheseShouldAllFail(int Num)
{
    EXPECT_ABORT_BEGIN
    TEST_ASSERT_TRUE(Num > 100);
    VERIFY_FAILS_END
}

TEST_CASE(1)
TEST_CASE(44)
TEST_CASE(99)
TEST_CASE(98)
void test_TheseAreEveryOther(int Num)
{
    if (Num & 1)
    {
        EXPECT_ABORT_BEGIN
        TEST_ASSERT_TRUE(Num > 100);
        VERIFY_FAILS_END
    }
    else
    {
        TEST_ASSERT_TRUE(Num < 100);
    }
}

void test_NormalPassesStillWork(void)
{
    TEST_ASSERT_TRUE(1);
}

void test_NormalFailsStillWork(void)
{
    EXPECT_ABORT_BEGIN
    TEST_ASSERT_TRUE(0);
    VERIFY_FAILS_END
}
