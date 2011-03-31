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
#include "TimerConfigurator.h"
#include "AT91SAM7X256.h"
#include "MockTimerInterruptConfigurator.h"

AT91S_PMC PmcPeripheral;
AT91S_TC  TimerCounter0Peripheral;
AT91S_PIO PioBPeripheral;

void setUp(void)
{
}

void tearDown(void)
{
}

void testEnablePeripheralClocksShouldEnableClockToTimer0Peripheral(void)
{
  AT91C_BASE_PMC->PMC_PCER = 0;
  Timer_EnablePeripheralClocks();
  TEST_ASSERT_EQUAL(
      TIMER0_CLOCK_ENABLE, 
      AT91C_BASE_PMC->PMC_PCER & TIMER0_CLOCK_ENABLE);
}

void testEnablePeripheralClocksShouldEnableClockToPIOBPeripheral(void)
{
  AT91C_BASE_PMC->PMC_PCER = 0;
  Timer_EnablePeripheralClocks();
  TEST_ASSERT_EQUAL(
      PIOB_CLOCK_ENABLE, 
      AT91C_BASE_PMC->PMC_PCER & PIOB_CLOCK_ENABLE);
}

void testResetShouldSetTimer0ClockDisableBit_DisableTimer0Interrupts_ClearStatusRegister(void)
{
  AT91C_BASE_TC0->TC_CCR = 0;
  AT91C_BASE_TC0->TC_IDR = 0;
  AT91C_BASE_TC0->TC_SR = 0xFFFFFFFF;
  Timer_Reset();
  TEST_ASSERT_EQUAL(0x00000002, AT91C_BASE_TC0->TC_CCR);
  TEST_ASSERT_EQUAL(0xffffffff, AT91C_BASE_TC0->TC_IDR);
  // CANNOT BE VERIFIED!! TEST_ASSERT_EQUAL(0X00000000, AT91C_BASE_TC0->TC_SR);
}

void testEnableOutputPinShouldEnable_TIOA0_DigitalOutput(void)
{
  AT91C_BASE_PIOB->PIO_PDR = 0;
  Timer_EnableOutputPin();
  TEST_ASSERT_EQUAL(TIOA0_PIN_MASK, AT91C_BASE_PIOB->PIO_PDR);
}

void testConfigureModeShouldConfigureTimer0ClockSourceForMasterClockDividedBy1024(void)
{
  AT91C_BASE_TC0->TC_CMR = 0;
  Timer_ConfigureMode();
  TEST_ASSERT_EQUAL(0x00000004, AT91C_BASE_TC0->TC_CMR & 0x00000007);
}

void testConfigureModeShouldConfigureTimer0ForWaveGeneration(void)
{
  AT91C_BASE_TC0->TC_CMR = 0;
  Timer_ConfigureMode();
  TEST_ASSERT_EQUAL(0x00008000, AT91C_BASE_TC0->TC_CMR & 0x00008000);
}

void testConfigureModeShouldConfigureTimer0ForUpModeWithAutomaticTriggerOnRCCompare(void)
{
  AT91C_BASE_TC0->TC_CMR = 0;
  Timer_ConfigureMode();
  TEST_ASSERT_EQUAL(0x00004000, AT91C_BASE_TC0->TC_CMR & 0x00006000);
}

void testConfigureModeShouldConfigureTimer0ToToggleTIOAOnRCCompare(void)
{
  AT91C_BASE_TC0->TC_CMR = 0;
  Timer_ConfigureMode();
  TEST_ASSERT_EQUAL(0x000C0000, AT91C_BASE_TC0->TC_CMR & 0x000C0000);
}

void testConfigurePeriodShouldConfigureRegisterCFor10msInterval(void)
{
  AT91C_BASE_TC0->TC_RC = 0;
  Timer_ConfigurePeriod();
  TEST_ASSERT_EQUAL(469, AT91C_BASE_TC0->TC_RC);
}

void testEnableShouldSetEnableFlagForTimer0(void)
{
  AT91C_BASE_TC0->TC_CCR = 0;
  Timer_Enable();
  TEST_ASSERT_EQUAL_INT(1, AT91C_BASE_TC0->TC_CCR);
}

void testConfigureInterruptHandler(void)
{
  Timer_DisableInterrupt_Expect();
  Timer_ResetSystemTime_Expect();
  Timer_ConfigureInterrupt_Expect();
  Timer_EnableInterrupt_Expect();

  Timer_ConfigureInterruptHandler();
}

void testStartShouldSetSoftwareTriggerFlag(void)
{
  AT91C_BASE_TC0->TC_CCR = 0;
  Timer_Start();
  TEST_ASSERT_EQUAL(0x04, AT91C_BASE_TC0->TC_CCR);
}
