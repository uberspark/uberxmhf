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

#ifndef UNITY_FIXTURE_INTERNALS_H_
#define UNITY_FIXTURE_INTERNALS_H_

typedef struct _UNITY_FIXTURE_T
{
    int Verbose;
    unsigned int RepeatCount;
    const char* NameFilter;
    const char* GroupFilter;
} UNITY_FIXTURE_T;

typedef void unityfunction();
void UnityTestRunner(unityfunction * setup,
        unityfunction * body,
        unityfunction * teardown,
        const char * printableName,
        const char * group,
        const char * name,
        const char * file, int line);

void UnityMalloc_StartTest();
void UnityMalloc_EndTest();
int UnityFailureCount();
int UnityGetCommandLineOptions(int argc, char* argv[]);
void UnityConcludeFixtureTest();

void UnityPointer_Set(void ** ptr, void * newValue);
void UnityPointer_UndoAllSets();
void UnityPointer_Init();

void UnityAssertEqualPointer(const void * expected,
                            const void * actual,
                            const char* msg,
                            const UNITY_LINE_TYPE lineNumber);

#endif /* UNITY_FIXTURE_INTERNALS_H_ */
