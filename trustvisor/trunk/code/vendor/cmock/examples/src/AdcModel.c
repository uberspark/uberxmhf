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

#include "AdcModel.h"
#include "TaskScheduler.h"
#include "TemperatureCalculator.h"
#include "TemperatureFilter.h"

bool AdcModel_DoGetSample(void)
{
  return TaskScheduler_DoAdc();
}

void AdcModel_ProcessInput(uint16 millivolts)
{
  TemperatureFilter_ProcessInput(TemperatureCalculator_Calculate(millivolts));
}

bool AdcModel_DoNothingExceptTestASpecialType(EXAMPLE_STRUCT_T ExampleStruct)
{
    //This doesn't really do anything. it's only here to make sure I can compare a struct.
    return FALSE;
}
bool AdModel_DoNothingExceptTestPointers(uint32* pExample)
{
    //This doesn't really do anything. it's only here to make sure I can compare a pointer value.
    return FALSE;
}

EXAMPLE_STRUCT_T AdcModel_DoNothingExceptReturnASpecialType(void)
{
    EXAMPLE_STRUCT_T example; //again, this just is here to test that I can return a struct
    example.x = 99;
    example.y = 1;
    return example;
}
