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
#include "TaskScheduler.h"

typedef struct _Task
{
  bool    doIt;
  uint32  period;
  uint32  startTime;
} Task;

typedef struct _TaskSchedulerInstance
{
  Task usart;
  Task adc;
} TaskSchedulerInstance;

static TaskSchedulerInstance this;

void TaskScheduler_Init(void)
{
  this.usart.doIt = FALSE;
  this.usart.startTime = 0;

  //The correct period
  this.usart.period = 1000;

  this.adc.doIt = FALSE;
  this.adc.startTime = 0;
  this.adc.period = 100;
}

void TaskScheduler_Update(uint32 time)
{
  if ((time - this.usart.startTime) >= this.usart.period)
  {
    this.usart.doIt = TRUE;
    this.usart.startTime = time - (time % this.usart.period);
  }

  if ((time - this.adc.startTime) >= this.adc.period)
  {
    this.adc.doIt = TRUE;
    this.adc.startTime = time - (time % this.adc.period);
  }
}

bool TaskScheduler_DoUsart(void)
{
  bool doIt = FALSE;

  if (this.usart.doIt)
  {
    doIt = TRUE;
    this.usart.doIt = FALSE;
  }

  return doIt;
}

bool TaskScheduler_DoAdc(void)
{
  bool doIt = FALSE;

  if (this.adc.doIt)
  {
    doIt = TRUE;
    this.adc.doIt = FALSE;
  }

  return doIt;
}

