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
#include "TimerInterruptConfigurator.h"
#include "MockTimerInterruptHandler.h"
#include "AT91SAM7X256.h"

AT91S_AIC AicPeripheral;
AT91S_TC  TimerCounter0Peripheral;

void setUp(void)
{
}

void tearDown(void)
{
}

void test_TIMER0_ID_MASK_ShouldBeCorrect(void)
{
  TEST_ASSERT_EQUAL(((uint32)0x1) << AT91C_ID_TC0, TIMER0_ID_MASK);
}

void testDisableInterruptDisablesTimer0InterruptInTheInterruptController(void)
{
  AT91C_BASE_AIC->AIC_IDCR = 0;
  Timer_DisableInterrupt();
  TEST_ASSERT_EQUAL(TIMER0_ID_MASK, AT91C_BASE_AIC->AIC_IDCR);
}

void testResetSystemTimeDelegatesTo_Timer_SetSystemTime_Appropriately(void)
{
  Timer_SetSystemTime_Expect(0);
  Timer_ResetSystemTime();
}

void testConfigureInterruptShouldSetInterruptHandlerAppropriately(void)
{
  AT91C_BASE_AIC->AIC_SVR[AT91C_ID_TC0] = (uint32)NULL;
  Timer_ConfigureInterrupt();
  TEST_ASSERT_EQUAL((uint32)Timer_InterruptHandler, AT91C_BASE_AIC->AIC_SVR[AT91C_ID_TC0]);
}

void testConfigureInterruptShouldSetInterruptLevelInSourceModeRegisterAppropriately(void)
{
  AT91C_BASE_AIC->AIC_SMR[AT91C_ID_TC0] = 0;
  Timer_ConfigureInterrupt();
  TEST_ASSERT_EQUAL(
      AT91C_AIC_SRCTYPE_INT_HIGH_LEVEL, 
      AT91C_BASE_AIC->AIC_SMR[AT91C_ID_TC0] & 0x00000060);
}

void testConfigureInterruptShouldSetInterruptPriorityInSourceModeRegisterAppropriately(void)
{
  AT91C_BASE_AIC->AIC_SMR[AT91C_ID_TC0] = 0;
  Timer_ConfigureInterrupt();
  TEST_ASSERT_EQUAL(1, AT91C_BASE_AIC->AIC_SMR[AT91C_ID_TC0] & 0x00000007);
}

void testConfigureInterruptShouldClearTimer0InterruptOnTheInterruptController(void)
{
  AT91C_BASE_AIC->AIC_ICCR = 0;
  Timer_ConfigureInterrupt();
  TEST_ASSERT_EQUAL(TIMER0_ID_MASK, AT91C_BASE_AIC->AIC_ICCR);
}

void testConfigureInterruptShouldEnableCompareInterruptForRegisterC(void)
{
  AT91C_BASE_TC0->TC_IER = 0;
  Timer_ConfigureInterrupt();
  TEST_ASSERT_EQUAL(AT91C_TC_CPCS, AT91C_BASE_TC0->TC_IER);
}

void testEnableInterruptShouldEnableTimer0InterruptsInInterruptCotroller(void)
{
  AT91C_BASE_AIC->AIC_IECR = 0;
  Timer_EnableInterrupt();
  TEST_ASSERT_EQUAL(TIMER0_ID_MASK, AT91C_BASE_AIC->AIC_IECR);
}
