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

#include <unity.h>

#include "Mocktv.h"
#include "audited-kv.h"

akv_ctx_t g_ctx;
/* static const char * key1 = "key one"; */
/* static const char * val1 = "value one"; */

void setUp(void)
{
  tv_pal_sections_init_Ignore();
  tv_pal_register_IgnoreAndReturn(0);
  akv_ctx_init(&g_ctx, "keyfile");
}

void tearDown(void)
{
  akv_ctx_release(&g_ctx);
}

void test_init(void)
{
  akv_ctx_t ctx;

  tv_pal_sections_init_Ignore();
  tv_pal_register_IgnoreAndReturn(0);
  TEST_ASSERT(!akv_ctx_init(&ctx, "keyfile"));
}

void test_init_detects_err(void)
{
  akv_ctx_t ctx;

  TEST_ASSERT(akv_ctx_init(&ctx, "keyfile"));
}

void test_release(void)
{
  TEST_ASSERT(!akv_ctx_release(&g_ctx));
}

void test_release_detects_err(void)
{
  TEST_ASSERT(akv_ctx_release(&g_ctx));
}

/* void test_add_succeeds(void) */
/* { */
/*   akv_cmd_ctx_t akv_cmd_ctx; */
/*   int rv; */
/*   rv = akv_db_add_begin(&g_ctx, &akv_cmd_ctx, key1, val1); */
/* } */
