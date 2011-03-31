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
#include "TimerConfigurator.h"
#include "TimerInterruptConfigurator.h"

void Timer_EnablePeripheralClocks(void)
{
  AT91C_BASE_PMC->PMC_PCER = TIMER0_CLOCK_ENABLE | PIOB_CLOCK_ENABLE;
}

void Timer_Reset(void)
{
  uint32 dummy;
  AT91C_BASE_TC0->TC_CCR = AT91C_TC_CLKDIS;
  AT91C_BASE_TC0->TC_IDR = 0xffffffff;
  dummy = AT91C_BASE_TC0->TC_SR;
  dummy = dummy;
}

void Timer_ConfigureMode(void)
{
  AT91C_BASE_TC0->TC_CMR = 0x000CC004; // ACPC=toggle TIOA on RC compare; mode=WAVE; WAVE_SEL=UP w/auto-trigger on RC compare; clock=MCK/1024
}

void Timer_ConfigurePeriod(void)
{
  AT91C_BASE_TC0->TC_RC = 469; // 10ms period for timer clock source of MCK/1024 with MCK=48054857
}

void Timer_EnableOutputPin(void)
{
  AT91C_BASE_PIOB->PIO_PDR = TIOA0_PIN_MASK;
}

void Timer_Enable(void)
{
  AT91C_BASE_TC0->TC_CCR = AT91C_TC_CLKEN;
}

void Timer_ConfigureInterruptHandler(void)
{
  Timer_DisableInterrupt();
  Timer_ResetSystemTime();
  Timer_ConfigureInterrupt();
  Timer_EnableInterrupt();
}

void Timer_Start(void)
{
  AT91C_BASE_TC0->TC_CCR = AT91C_TC_SWTRG;
}

