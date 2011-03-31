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
#include "UsartConductor.h"
#include "MockUsartModel.h"
#include "MockUsartHardware.h"
#include "MockTaskScheduler.h"

void setUp(void)
{
}

void tearDown(void)
{
}

void testShouldInitializeHardwareWhenInitCalled(void)
{
  UsartModel_GetBaudRateRegisterSetting_ExpectAndReturn(4);
  UsartModel_GetWakeupMessage_ExpectAndReturn("Hey there!");
  UsartHardware_TransmitString_Expect("Hey there!");
  UsartHardware_Init_Expect(4);

  UsartConductor_Init();
}

void testRunShouldNotDoAnythingIfSchedulerSaysItIsNotTimeYet(void)
{
  TaskScheduler_DoUsart_ExpectAndReturn(FALSE);

  UsartConductor_Run();
}

void testRunShouldGetCurrentTemperatureAndTransmitIfSchedulerSaysItIsTime(void)
{
  TaskScheduler_DoUsart_ExpectAndReturn(TRUE);
  UsartModel_GetFormattedTemperature_ExpectAndReturn("hey there");
  UsartHardware_TransmitString_Expect("hey there");

  UsartConductor_Run();
}
