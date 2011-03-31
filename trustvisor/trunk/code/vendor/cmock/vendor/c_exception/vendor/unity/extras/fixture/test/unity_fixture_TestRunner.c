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

//- Copyright (c) 2010 James Grenning and Contributed to Unity Project
/* ==========================================
    Unity Project - A Test Framework for C
    Copyright (c) 2007 Mike Karlesky, Mark VanderVoord, Greg Williams
    [Released under MIT License. Please refer to license.txt for details]
========================================== */

#include "unity_fixture.h"

TEST_GROUP_RUNNER(UnityFixture)
{
    RUN_TEST_CASE(UnityFixture, PointerSetting);
    RUN_TEST_CASE(UnityFixture, ForceMallocFail);
    RUN_TEST_CASE(UnityFixture, ReallocSmallerIsUnchanged);
    RUN_TEST_CASE(UnityFixture, ReallocSameIsUnchanged);
    RUN_TEST_CASE(UnityFixture, ReallocLargerNeeded);
    RUN_TEST_CASE(UnityFixture, ReallocNullPointerIsLikeMalloc);
    RUN_TEST_CASE(UnityFixture, ReallocSizeZeroFreesMemAndReturnsNullPointer);
    RUN_TEST_CASE(UnityFixture, CallocFillsWithZero);
    RUN_TEST_CASE(UnityFixture, PointerSet);
}

TEST_GROUP_RUNNER(UnityCommandOptions)
{
    RUN_TEST_CASE(UnityCommandOptions, DefaultOptions);
    RUN_TEST_CASE(UnityCommandOptions, OptionVerbose);
    RUN_TEST_CASE(UnityCommandOptions, OptionSelectTestByGroup);
    RUN_TEST_CASE(UnityCommandOptions, OptionSelectTestByName);
    RUN_TEST_CASE(UnityCommandOptions, OptionSelectRepeatTestsDefaultCount);
    RUN_TEST_CASE(UnityCommandOptions, OptionSelectRepeatTestsSpecificCount);
    RUN_TEST_CASE(UnityCommandOptions, MultipleOptions);
    RUN_TEST_CASE(UnityCommandOptions, MultipleOptionsDashRNotLastAndNoValueSpecified);
}

TEST_GROUP_RUNNER(LeakDetection)
{
    RUN_TEST_CASE(LeakDetection, DetectsLeak);
    RUN_TEST_CASE(LeakDetection, BufferOverrunFoundDuringFree);
    RUN_TEST_CASE(LeakDetection, BufferOverrunFoundDuringRealloc);
}
