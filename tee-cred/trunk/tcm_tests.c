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
#include "tcm.h"

tcm_handle_t tcm_handle;

void setUp(void)
{
  tcm_init(&tcm_handle, NULL, NULL, 0);
}

void tearDown(void)
{
  tcm_release(&tcm_handle);
}

void test_tcm_init_null_handle_error(void)
{
  TEST_ASSERT_EQUAL(TCM_ERR_PARAM, tcm_init(NULL, NULL, NULL, 0));
}

void test_tcm_init_null_params_ok(void)
{
  tcm_handle_t tcm_handle;
  TEST_ASSERT_EQUAL(TCM_ERR_OK, tcm_init(&tcm_handle, NULL, NULL, 0));
}

void test_tcm_release_null_ok(void)
{
  tcm_release(NULL);
}

void test_tcm_release_uninitd_ok(void)
{
  tcm_handle_t tcm_handle;
  tcm_release(&tcm_handle);
}

void test_tcm_release_initd_ok(void)
{
  tcm_handle_t tcm_handle;
  tcm_init(&tcm_handle, NULL, NULL, 0);
  tcm_release(&tcm_handle);
}

void test_tcm_db_add_null_handle_error(void)
{
  TEST_ASSERT_EQUAL(TCM_ERR_PARAM, tcm_db_add(NULL, NULL, NULL));
}

void test_tcm_db_add_null_key_error(void)
{
  TEST_ASSERT_EQUAL(TCM_ERR_PARAM, tcm_db_add(&tcm_handle, NULL, "foo"));
}

void test_tcm_db_add_null_val_error(void)
{
  TEST_ASSERT_EQUAL(TCM_ERR_PARAM, tcm_db_add(&tcm_handle, "foo", NULL));
}

