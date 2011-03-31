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
#include "TimerInterruptHandler.h"
#include "AT91SAM7X256.h"

AT91S_TC  TimerCounter0Peripheral;

void setUp(void)
{
}

void tearDown(void)
{
}

void testSetAndGetSystemTime(void)
{
  Timer_SetSystemTime(0);
  TEST_ASSERT_EQUAL(0, Timer_GetSystemTime());

  Timer_SetSystemTime(129837);
  TEST_ASSERT_EQUAL(129837, Timer_GetSystemTime());

  Timer_SetSystemTime(UINT32_MAX);
  TEST_ASSERT_EQUAL(UINT32_MAX, Timer_GetSystemTime());
}

void testInterruptHandlerShouldIncrementSystemTimeOnlyIfStatusHasCompareRegisterCOverflowBitSet(void)
{
  Timer_SetSystemTime(0);
  AT91C_BASE_TC0->TC_SR = 0;
  Timer_InterruptHandler();
  TEST_ASSERT_EQUAL(0, Timer_GetSystemTime());

  Timer_SetSystemTime(0);
  AT91C_BASE_TC0->TC_SR = ~AT91C_TC_CPCS;
  Timer_InterruptHandler();
  TEST_ASSERT_EQUAL(0, Timer_GetSystemTime());

  Timer_SetSystemTime(0);
  AT91C_BASE_TC0->TC_SR = AT91C_TC_CPCS;
  Timer_InterruptHandler();
  TEST_ASSERT(Timer_GetSystemTime() > 0);

  Timer_SetSystemTime(0);
  AT91C_BASE_TC0->TC_SR = 0xffffffff;
  Timer_InterruptHandler();
  TEST_ASSERT(Timer_GetSystemTime() > 0);
}

void testInterruptHandlerShouldIncrementSystemTimerBy_10(void)
{
  Timer_SetSystemTime(0);
  AT91C_BASE_TC0->TC_SR = AT91C_TC_CPCS;
  Timer_InterruptHandler();
  TEST_ASSERT_EQUAL(10, Timer_GetSystemTime());

  AT91C_BASE_TC0->TC_SR = AT91C_TC_CPCS;
  Timer_InterruptHandler();
  TEST_ASSERT_EQUAL(20, Timer_GetSystemTime());

  Timer_SetSystemTime(39426857);
  AT91C_BASE_TC0->TC_SR = AT91C_TC_CPCS;
  Timer_InterruptHandler();
  TEST_ASSERT_EQUAL(39426867, Timer_GetSystemTime());
}
