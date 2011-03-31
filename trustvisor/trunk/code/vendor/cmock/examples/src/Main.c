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

#include "IntrinsicsWrapper.h"
#include "Executor.h"

#include "Model.h"
#include "TaskScheduler.h"
#include "TemperatureCalculator.h"
#include "TemperatureFilter.h"

#include "UsartConductor.h"
#include "UsartHardware.h"
#include "UsartConfigurator.h"
#include "UsartPutChar.h"
#include "UsartModel.h"
#include "UsartBaudRateRegisterCalculator.h"
#include "UsartTransmitBufferStatus.h"

#include "TimerConductor.h"
#include "TimerHardware.h"
#include "TimerConfigurator.h"
#include "TimerInterruptConfigurator.h"
#include "TimerInterruptHandler.h"
#include "TimerModel.h"

#include "AdcConductor.h"
#include "AdcHardware.h"
#include "AdcHardwareConfigurator.h"
#include "AdcTemperatureSensor.h"
#include "AdcModel.h"

int AppMain(void)
{
  Executor_Init();

  while(Executor_Run());
  
  return 0;
}

#ifndef TEST
int main(void)
{
  return AppMain();
}
#endif // TEST
