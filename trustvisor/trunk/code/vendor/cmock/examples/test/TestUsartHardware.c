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
#include "UsartHardware.h"
#include "AT91SAM7X256.h"
#include "MockUsartConfigurator.h"
#include "MockUsartPutChar.h"

void setUp(void)
{
}

void tearDown(void)
{
}

void testInitShouldConfigureUsartPeripheralByCallingConfiguratorAppropriately(void)
{
  Usart_ConfigureUsartIO_Expect();
  Usart_EnablePeripheralClock_Expect();
  Usart_Reset_Expect();
  Usart_ConfigureMode_Expect();
  Usart_SetBaudRateRegister_Expect(73);
  Usart_Enable_Expect();

  UsartHardware_Init(73);
}

void testTransmitStringShouldSendDesiredStringOutUsingUsart(void)
{
  Usart_PutChar_Expect('h');
  Usart_PutChar_Expect('e');
  Usart_PutChar_Expect('l');
  Usart_PutChar_Expect('l');
  Usart_PutChar_Expect('o');
  
  UsartHardware_TransmitString("hello");
}
