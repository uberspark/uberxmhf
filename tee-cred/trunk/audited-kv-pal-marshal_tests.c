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
#include <tzmarshal.h>

#include "Mocksvcapi.h"
#include "audited-kv-pal.h"

static tzi_encode_buffer_t *g_psInBuf, *g_psOutBuf;
static const char * key1 = "key one";
static const size_t key1_len = 8;
static const char * val1 = "value one";
static const size_t val1_len = 10;

void setUp(void)
{
  g_psInBuf = malloc(4096);
  g_psOutBuf = malloc(4096);
  TZIEncodeBufInit(g_psInBuf, 4096);
  TZIEncodeBufInit(g_psOutBuf, 4096);
}

void tearDown(void)
{
  free(g_psInBuf);
  free(g_psOutBuf);
}

void testAuditedAdd(void)
{
  tz_return_t rv;
  int cmd_id;
  void *audit_nonce;
  size_t audit_nonce_len;
  void *audit_string;
  size_t audit_string_len;
  uint8_t audit_token[] = {0xde, 0xad, 0xbe, 0xef};

  /* start audited 'add' */
  TZIEncodeUint32(g_psInBuf, AKVP_DB_ADD);
  TZIEncodeArray(g_psInBuf, key1, key1_len);
  TZIEncodeArray(g_psInBuf, val1, val1_len);
  TEST_ASSERT(!(TZIDecodeGetError(g_psInBuf)));

  svc_time_elapsed_us_IgnoreAndReturn(0);
  svc_utpm_rand_block_IgnoreAndReturn(0);

  TZIEncodeToDecode(g_psInBuf);
  audited_kv_pal(AKVP_START_AUDITED_CMD, g_psInBuf, g_psOutBuf, &rv);
  TZIEncodeToDecode(g_psOutBuf);

  TEST_ASSERT(!rv);
  cmd_id = TZIDecodeUint32(g_psOutBuf);
  audit_nonce = TZIDecodeArraySpace(g_psOutBuf, &audit_nonce_len);
  audit_string = TZIDecodeArraySpace(g_psOutBuf, &audit_string_len);
  TEST_ASSERT(!(TZIDecodeGetError(g_psOutBuf)));

  TEST_ASSERT_NOT_NULL(audit_nonce);
  TEST_ASSERT_NOT_NULL(audit_string);

  TEST_ASSERT_EQUAL_STRING("ADD{key=\"key one\"}",
                           audit_string);

  /* execute audited 'add' */

  TZIEncodeBufReInit(g_psInBuf);
  TZIEncodeBufReInit(g_psOutBuf);

  TZIEncodeUint32(g_psInBuf, cmd_id);
  TZIEncodeArray(g_psInBuf, audit_token, sizeof(audit_token));
  TEST_ASSERT(!(TZIDecodeGetError(g_psInBuf)));

  TZIEncodeToDecode(g_psInBuf);
  audited_kv_pal(AKVP_EXECUTE_AUDITED_CMD, g_psInBuf, g_psOutBuf, &rv);
  TZIEncodeToDecode(g_psOutBuf);

  TEST_ASSERT(!rv);
}
