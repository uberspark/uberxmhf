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

#include <unity.h>

#include "tcm.h"

#include "Mockaudited-kv.h"
#include "Mockaudit.h"

audit_ctx_t audit_ctx;
tcm_ctx_t tcm_ctx;
akv_ctx_t akv_ctx;

void setUp(void)
{
  tcm_init(&tcm_ctx, &audit_ctx, &akv_ctx);
}

void tearDown(void)
{
  tcm_release(&tcm_ctx);
}

void test_tcm_init_null_ctx_error(void)
{
  TEST_ASSERT_EQUAL(TCM_EINVAL, tcm_init(NULL, NULL, NULL));
}

void test_tcm_init_null_params_err(void)
{
  tcm_ctx_t tcm_ctx;
  TEST_ASSERT_EQUAL(TCM_EINVAL, tcm_init(&tcm_ctx, NULL, NULL));
  TEST_ASSERT_EQUAL(TCM_EINVAL, tcm_init(&tcm_ctx, &audit_ctx, NULL));
  TEST_ASSERT_EQUAL(TCM_EINVAL, tcm_init(&tcm_ctx, NULL, &akv_ctx));
}

void test_tcm_init_saves_audit_ctx(void)
{
  tcm_ctx_t tcm_ctx;
  audit_ctx_t audit_ctx;
  tcm_init(&tcm_ctx, &audit_ctx, NULL);
  TEST_ASSERT_EQUAL_PTR(&audit_ctx, tcm_ctx.audit_ctx);
}

void test_tcm_release_null_ok(void)
{
  tcm_release(NULL);
}

void test_tcm_release_uninitd_ok(void)
{
  tcm_ctx_t tcm_ctx;
  tcm_release(&tcm_ctx);
}

void test_tcm_release_initd_ok(void)
{
  tcm_ctx_t tcm_ctx;
  tcm_init(&tcm_ctx, NULL, NULL);
  tcm_release(&tcm_ctx);
}

void test_tcm_db_add_null_ctx_error(void)
{
  TEST_ASSERT_EQUAL(TCM_EINVAL, tcm_db_add(NULL, NULL, NULL));
}

void test_tcm_db_add_null_key_error(void)
{
  TEST_ASSERT_EQUAL(TCM_EINVAL, tcm_db_add(&tcm_ctx, NULL, "foo"));
}

void test_tcm_db_add_null_val_error(void)
{
  TEST_ASSERT_EQUAL(TCM_EINVAL, tcm_db_add(&tcm_ctx, "foo", NULL));
}

void test_tcm_db_add_gets_audit_challenge(void)
{
  /* akv_begin_db_add_ExpectAndReturn(NULL, */
  /*                                  NULL, */
  /*                                  NULL, */
  /*                                  NULL, */
  /*                                  NULL, */
  /*                                  NULL, */
  /*                                  NULL, */
  /*                                  NULL, */
  /*                                  0); */
  akv_begin_db_add_IgnoreAndReturn(0);

  tcm_db_add(&tcm_ctx, "key", "value");
}

/* void test_tcm_db_add_gets_audit_token(void) */
/* { */
/*   audit_get_token_ExpectAndReturn(&audit_ctx, */
/*                                   "", 0, ); */
/* } */
