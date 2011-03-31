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

#include "Types.h"
#include "AdcTemperatureSensor.h"

static inline uint32 ConvertAdcCountsToPicovolts(uint32 counts); 
static inline uint16 ConvertPicovoltsToMillivolts(uint32 picovolts);

//
// PUBLIC METHODS
//

void Adc_StartTemperatureSensorConversion(void)
{
  AT91C_BASE_ADC->ADC_CR = AT91C_ADC_START;
}

bool Adc_TemperatureSensorSampleReady(void)
{
  return ((AT91C_BASE_ADC->ADC_SR & AT91C_ADC_EOC4) == AT91C_ADC_EOC4);
}

uint16 Adc_ReadTemperatureSensor(void)
{
  uint32 picovolts = ConvertAdcCountsToPicovolts(AT91C_BASE_ADC->ADC_CDR4);
  return ConvertPicovoltsToMillivolts(picovolts);
}

//
// PRIVATE HELPERS
//

static inline uint32 ConvertAdcCountsToPicovolts(uint32 counts)
{
  // ADC bit weight at 10-bit resolution with 3.0V reference = 2.9296875 mV/LSB
  uint32 picovoltsPerAdcCount = 2929688;

  // Shift decimal point by 6 places to preserve accuracy in fixed-point math
  return counts * picovoltsPerAdcCount;
}

static inline uint16 ConvertPicovoltsToMillivolts(uint32 picovolts)
{
  const uint32 halfMillivoltInPicovolts = 500000;
  const uint32 picovoltsPerMillivolt = 1000000;
    
  // Add 0.5 mV to result so that truncation yields properly rounded result
  picovolts += halfMillivoltInPicovolts;

  // Divide appropriately to convert to millivolts
  return (uint16)(picovolts / picovoltsPerMillivolt);
}

