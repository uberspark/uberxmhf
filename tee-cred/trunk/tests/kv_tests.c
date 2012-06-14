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
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
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

#include "kv.h"

#include <unity.h>

#include <string.h>

static kv_ctx_t *kv_ctx=NULL;
static const char * key1 = "key one";
static const size_t key1_len = 8;
static const char * val1 = "value one";
static const size_t val1_len = 10;

/* static const char * key2 = "key two"; */
/* static const size_t key2_len = 8; */
/* static const char * val2 = "value two"; */
/* static const size_t val2_len = 10; */


void setUp(void)
{
  kv_ctx=kv_ctx_new();
}

void tearDown(void)
{
  kv_ctx_del(kv_ctx);
}

void test_add_to_empty_succeeds(void)
{
  TEST_ASSERT(!kv_add(kv_ctx, key1, key1_len, val1, val1_len));
}

void test_add_duplicate_fails(void)
{
  TEST_ASSERT(!kv_add(kv_ctx, key1, key1_len, val1, val1_len));
  TEST_ASSERT_EQUAL(KV_EEXISTS, kv_add(kv_ctx, key1, key1_len, val1, val1_len));
}

void test_get_empty_fails(void)
{
  TEST_ASSERT_EQUAL(KV_ENOTFOUND, kv_get(kv_ctx, key1, key1_len, NULL, NULL));
}

void test_get_existing_works(void)
{
  const void *val;
  size_t val_len;

  TEST_ASSERT(!kv_add(kv_ctx, key1, key1_len, val1, val1_len));
  TEST_ASSERT(!kv_get(kv_ctx, key1, key1_len, &val, &val_len));
  TEST_ASSERT_EQUAL(val1_len, val_len);
  TEST_ASSERT_EQUAL_STRING(val1, val);
}
