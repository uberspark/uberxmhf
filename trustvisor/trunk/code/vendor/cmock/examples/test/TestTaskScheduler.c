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
#include "Types.h"
#include "TaskScheduler.h"

void setUp(void)
{
  TaskScheduler_Init();
}

void tearDown(void)
{
}

void testShouldScheduleUsartTaskAfter1000ms(void)
{
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoUsart());

  TaskScheduler_Update(999);
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoUsart());

  TaskScheduler_Update(1000);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoUsart());
}

void testShouldClearUsartDoFlagAfterReported(void)
{
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoUsart());
  TaskScheduler_Update(1000);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoUsart());
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoUsart());
}

void testShouldScheduleUsartTaskEvery1000ms(void)
{
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoUsart());

  TaskScheduler_Update(1300);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoUsart());

  TaskScheduler_Update(2000);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoUsart());

  TaskScheduler_Update(3100);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoUsart());
}

void testShouldScheduleUsartTaskOnlyOncePerPeriod(void)
{
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoUsart());
  TaskScheduler_Update(1000);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoUsart());
  TaskScheduler_Update(1001);
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoUsart());
  TaskScheduler_Update(1999);
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoUsart());
  TaskScheduler_Update(2000);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoUsart());
}

void testShouldScheduleAdcTaskAfter100ms(void)
{
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoAdc());

  TaskScheduler_Update(99);
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoAdc());

  TaskScheduler_Update(100);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoAdc());
}

void testShouldClearAdcDoFlagAfterReported(void)
{
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoAdc());
  TaskScheduler_Update(100);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoAdc());
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoAdc());
}

void testShouldScheduleAdcTaskEvery100ms(void)
{
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoAdc());

  TaskScheduler_Update(121);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoAdc());

  TaskScheduler_Update(200);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoAdc());

  TaskScheduler_Update(356);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoAdc());
}

void testShouldScheduleAdcTaskOnlyOncePerPeriod(void)
{
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoAdc());
  TaskScheduler_Update(100);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoAdc());
  TaskScheduler_Update(101);
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoAdc());
  TaskScheduler_Update(199);
  TEST_ASSERT_EQUAL(FALSE, TaskScheduler_DoAdc());
  TaskScheduler_Update(200);
  TEST_ASSERT_EQUAL(TRUE, TaskScheduler_DoAdc());
}
