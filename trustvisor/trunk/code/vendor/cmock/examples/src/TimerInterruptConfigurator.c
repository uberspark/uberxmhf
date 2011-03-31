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
#include "TimerInterruptConfigurator.h"
#include "TimerInterruptHandler.h"

static inline void SetInterruptHandler(void);
static inline void ConfigureInterruptSourceModeRegister(void);
static inline void ClearInterrupt(void);
static inline void EnableCompareInterruptForRegisterC(void);

void Timer_DisableInterrupt(void)
{
  AT91C_BASE_AIC->AIC_IDCR = TIMER0_ID_MASK;
}

void Timer_ResetSystemTime(void)
{
  Timer_SetSystemTime(0);
}

void Timer_ConfigureInterrupt(void)
{
  SetInterruptHandler();
  ConfigureInterruptSourceModeRegister();
  ClearInterrupt();
  EnableCompareInterruptForRegisterC();
}

void Timer_EnableInterrupt(void)
{
  AT91C_BASE_AIC->AIC_IECR = TIMER0_ID_MASK;
}

//
// Helpers
//

static inline void SetInterruptHandler(void)
{
  AT91C_BASE_AIC->AIC_SVR[AT91C_ID_TC0] = (uint32)Timer_InterruptHandler;
}

static inline void ConfigureInterruptSourceModeRegister(void)
{
  AT91C_BASE_AIC->AIC_SMR[AT91C_ID_TC0] = 1;
}

static inline void ClearInterrupt(void)
{
  AT91C_BASE_AIC->AIC_ICCR = TIMER0_ID_MASK;
}

static inline void EnableCompareInterruptForRegisterC(void)
{
  AT91C_BASE_TC0->TC_IER = AT91C_TC_CPCS;
}
