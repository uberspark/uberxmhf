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
#include "AdcConductor.h"
#include "AdcModel.h"
#include "AdcHardware.h"

void AdcConductor_Init(void)
{
  AdcHardware_Init();
}

void AdcConductor_Run(void)
{
  if (AdcModel_DoGetSample() && AdcHardware_GetSampleComplete())
  {
    AdcModel_ProcessInput(AdcHardware_GetSample());
    AdcHardware_StartConversion();
  }
}

bool AdcConductor_JustHereToTest(void)
{
    EXAMPLE_STRUCT_T ExampleStruct;
    ExampleStruct.x = 5;
    ExampleStruct.y = 7;

    return AdcModel_DoNothingExceptTestASpecialType(ExampleStruct);
}

bool AdcConductor_AlsoHereToTest(void)
{
    EXAMPLE_STRUCT_T example = AdcModel_DoNothingExceptReturnASpecialType();

    return ((example.x == 99) && (example.y == 1));
}

bool AdcConductor_YetAnotherTest(void)
{
    uint32 example = 3;

    return AdModel_DoNothingExceptTestPointers(&example);
}

