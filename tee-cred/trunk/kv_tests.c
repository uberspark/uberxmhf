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

#include "kv.h"

#include <unity.h>

#include <string.h>

static kv_ctx_t *kv_ctx=NULL;

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
  char *key = "key";
  size_t key_len = strlen(key)+1;
  char *val = "val";
  size_t val_len = strlen(val)+1;

  TEST_ASSERT(!kv_add(kv_ctx, key, key_len, val, val_len));
}

void test_add_duplicate_fails(void)
{
  char *key = "key";
  size_t key_len = strlen(key)+1;
  char *val = "val";
  size_t val_len = strlen(val)+1;

  TEST_ASSERT(!kv_add(kv_ctx, key, key_len, val, val_len));
  TEST_ASSERT_EQUAL(KV_EEXISTS, kv_add(kv_ctx, key, key_len, val, val_len));
}
