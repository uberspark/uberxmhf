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
#include "UsartConfigurator.h"

void Usart_ConfigureUsartIO(void)
{
  AT91C_BASE_PIOA->PIO_ASR = USART0_TX_PIN;
  AT91C_BASE_PIOA->PIO_BSR = 0;
  AT91C_BASE_PIOA->PIO_PDR = USART0_TX_PIN;
}

void Usart_EnablePeripheralClock(void)
{
  AT91C_BASE_PMC->PMC_PCER = ((uint32)1) << USART0_CLOCK_ENABLE;
}

void Usart_Reset(void)
{
  AT91C_BASE_US0->US_IDR = 0xffffffff;
  AT91C_BASE_US0->US_CR = AT91C_US_RSTRX | AT91C_US_RSTTX | AT91C_US_RXDIS | AT91C_US_TXDIS;
}

void Usart_ConfigureMode(void)
{
  AT91C_BASE_US0->US_MR = AT91C_US_USMODE_NORMAL |
                          AT91C_US_NBSTOP_1_BIT |
                          AT91C_US_PAR_NONE |
                          AT91C_US_CHRL_8_BITS |
                          AT91C_US_CLKS_CLOCK;
}

void Usart_SetBaudRateRegister(uint8 baudRateRegisterSetting)
{
  AT91C_BASE_US0->US_BRGR = baudRateRegisterSetting;
}

void Usart_Enable(void)
{
  AT91C_BASE_US0->US_CR = AT91C_US_TXEN;
}
