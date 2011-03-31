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
#include "TemperatureFilter.h"
#include <math.h>

void setUp(void)
{
  TemperatureFilter_Init();
}

void tearDown(void)
{
}

void testShouldInitializeTemeratureToInvalidValue(void)
{
  TemperatureFilter_Init();
  TEST_ASSERT_FLOAT_WITHIN(0.0001f, -INFINITY, TemperatureFilter_GetTemperatureInCelcius());
}

void testShouldInitializeTemperatureAfterCallToInit(void)
{
  TemperatureFilter_Init();
  TemperatureFilter_ProcessInput(17.8f);
  TEST_ASSERT_FLOAT_WITHIN(0.0001f, 17.8f, TemperatureFilter_GetTemperatureInCelcius());

  TemperatureFilter_Init();
  TemperatureFilter_ProcessInput(32.6f);
  TEST_ASSERT_FLOAT_WITHIN(0.0001f, 32.6f, TemperatureFilter_GetTemperatureInCelcius());
}

void setValueAndVerifyResponse(float input, float response)
{
  float actual;
  TemperatureFilter_ProcessInput(input);
  actual = TemperatureFilter_GetTemperatureInCelcius();
  TEST_ASSERT_FLOAT_WITHIN(0.0001f, response, actual);
}

void testShouldWeightEachSubsequentValueBy25PercentAfterInitialValue(void)
{
  TemperatureFilter_Init();
  setValueAndVerifyResponse(0.0f, 0.0f);
  setValueAndVerifyResponse(10.0f, 2.5f);
  setValueAndVerifyResponse(10.0f, 4.375f);
  setValueAndVerifyResponse(10.0f, 5.78125f);

  TemperatureFilter_Init();
  setValueAndVerifyResponse(100.0f, 100.0f);
  setValueAndVerifyResponse(0.0f, 75.0f);
  setValueAndVerifyResponse(0.0f, 56.25f);
  setValueAndVerifyResponse(0.0f, 42.1875f);
}

void setInvalidTemperatureAndVerifyReinitialized(float invalidTemperature)
{
  TemperatureFilter_Init();
  setValueAndVerifyResponse(100.0f, 100.0f);
  setValueAndVerifyResponse(invalidTemperature, -INFINITY);
  setValueAndVerifyResponse(14.3f, 14.3f);
}

void testShouldResetAverageIfPassedInfinityOrInvalidValue(void)
{
  setInvalidTemperatureAndVerifyReinitialized(-INFINITY);
  setInvalidTemperatureAndVerifyReinitialized(+INFINITY);
  setInvalidTemperatureAndVerifyReinitialized(+NAN);
  setInvalidTemperatureAndVerifyReinitialized(-NAN);
}
