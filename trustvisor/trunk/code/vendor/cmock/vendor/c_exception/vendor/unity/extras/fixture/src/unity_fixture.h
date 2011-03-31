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

#ifndef UNITY_FIXTURE_H_
#define UNITY_FIXTURE_H_

#include "unity.h"
#include "unity_internals.h"
#include "unity_fixture_malloc_overrides.h"
#include "unity_fixture_internals.h"

int UnityMain(int argc, char* argv[], void (*runAllTests)());


#define TEST_GROUP(group)\
    int TEST_GROUP_##group = 0

#define TEST_SETUP(group) void TEST_##group##_SETUP()

#define TEST_TEAR_DOWN(group) void TEST_##group##_TEAR_DOWN()


#define TEST(group, name) \
    void TEST_##group##_##name##_testBody();\
    void TEST_##group##_##name##_run()\
    {\
        UnityTestRunner(TEST_##group##_SETUP,\
             TEST_##group##_##name##_testBody,\
            TEST_##group##_TEAR_DOWN,\
            "TEST(" #group ", " #name ")",\
            #group, #name,\
            __FILE__, __LINE__);\
    }\
    void  TEST_##group##_##name##_testBody()

#define IGNORE_TEST(group, name) \
    void TEST_##group##_##name##_testBody();\
    void TEST_##group##_##name##_run()\
    {\
    }\
    void  TEST_##group##_##name##_testBody()

#define DECLARE_TEST_CASE(group, name) \
    void TEST_##group##_##name##_run()

#define RUN_TEST_CASE(group, name) \
        DECLARE_TEST_CASE(group, name);\
    TEST_##group##_##name##_run();

//This goes at the bottom of each test file or in a separate c file
#define TEST_GROUP_RUNNER(group)\
    void TEST_##group##_GROUP_RUNNER_runAll();\
    void TEST_##group##_GROUP_RUNNER()\
    {\
        TEST_##group##_GROUP_RUNNER_runAll();\
    }\
    void TEST_##group##_GROUP_RUNNER_runAll()

//Call this from main
#define RUN_TEST_GROUP(group)\
    void TEST_##group##_GROUP_RUNNER();\
    TEST_##group##_GROUP_RUNNER();

//CppUTest Compatibility Macros
#define UT_PTR_SET(ptr, newPointerValue)               UnityPointer_Set((void**)&ptr, (void*)newPointerValue)
#define TEST_ASSERT_POINTERS_EQUAL(expected, actual)   TEST_ASSERT_EQUAL_PTR(expected, actual)
#define TEST_ASSERT_BYTES_EQUAL(expected, actual)      TEST_ASSERT_EQUAL_HEX8(0xff & (expected), 0xff & (actual))
#define FAIL(message)                                  TEST_FAIL((message))
#define CHECK(condition)                               TEST_ASSERT_TRUE((condition))
#define LONGS_EQUAL(expected, actual)                  TEST_ASSERT_EQUAL_INT((expected), (actual))
#define STRCMP_EQUAL(expected, actual)                 TEST_ASSERT_EQUAL_STRING((expected), (actual))
#define DOUBLES_EQUAL(expected, actual, delta)         TEST_ASSERT_FLOAT_WITHIN(((expected), (actual), (delta))

void UnityMalloc_MakeMallocFailAfterCount(int count);

#endif /* UNITY_FIXTURE_H_ */
