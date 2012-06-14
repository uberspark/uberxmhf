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
#include <tzmarshal.h>

#include "Mocksvcapi.h"
#include "audited-kv-pal.h"

static tzi_encode_buffer_t *g_psInBuf, *g_psOutBuf;
static const char * key1 = "key one";
static const size_t key1_len = 8;
static const char * val1 = "value one";
static const size_t val1_len = 10;
static const char * audit_pub = 
  "-----BEGIN PUBLIC KEY-----\n"
  "MIIBIDANBgkqhkiG9w0BAQEFAAOCAQ0AMIIBCAKCAQEAtZi3Nsijw8LOFW6oTu5O\n"
  "5/QKno3Z5c55iFrsmz8Y2Dy5pMyKDOmhNPbDO0EwZBPb66U9PgkPSdlihlh3DNEo\n"
  "14xRA+rrhMqCFGVK86OzCv+tOlw0KbMXaZoYdJHkRSw4bVbIVVhYozJjcVRoaP2v\n"
  "ed5x+KqX8mIxDg+jgg9Tb5z4GIJ9wcr2lOOY0GmSinItFAnyckSOJ0xqddmqWTmO\n"
  "OvV05RdxykPgI7MR+7X3guTy3hpvA4N08dFOS3Hq7RM9tR5c2DEWRaFceW2YqKkU\n"
  "3F5ODi/PefYVc0Y2YFUdmawJsqFlotfVd5JuKAGK3GzERKXJ3q4aTUn22qaU+EOX\n"
  "TwIBAw==\n"
  "-----END PUBLIC KEY-----\n";

void setUp(void)
{
  g_psInBuf = malloc(4096);
  g_psOutBuf = malloc(4096);
  TZIEncodeBufInit(g_psInBuf, 4096);
  TZIEncodeBufInit(g_psOutBuf, 4096);

  TZIEncodeBufF(g_psInBuf, "%"TZI_ESTR, audit_pub);
  TZIEncodeToDecode(g_psInBuf);

  {
    tz_return_t rv;
    audited_kv_pal(AKVP_INIT, g_psInBuf, g_psOutBuf, &rv);
    TEST_ASSERT_EQUAL(0, rv);
  }
  TZIEncodeBufReInit(g_psInBuf);
}

void tearDown(void)
{
  free(g_psInBuf);
  free(g_psOutBuf);
}

void testAuditedAddSucceeds(void)
{
  tz_return_t rv;
  int cmd_id;
  void *audit_nonce;
  size_t audit_nonce_len;
  void *audit_string;
  size_t audit_string_len;
  uint8_t audit_token[] = {0xde, 0xad, 0xbe, 0xef};

  TEST_IGNORE_MESSAGE("test doesn't generate correct audit token yet");

  /* start audited 'add' */
  rv = TZIEncodeBufF(g_psInBuf,
                     "%"TZI_EU32 "%"TZI_ESTR "%"TZI_ESTR,
                     AKVP_DB_ADD, key1, val1);
  TEST_ASSERT_EQUAL(0, rv);

  svc_time_elapsed_us_IgnoreAndReturn(0);
  svc_utpm_rand_block_IgnoreAndReturn(0);

  TZIEncodeToDecode(g_psInBuf);
  audited_kv_pal(AKVP_START_AUDITED_CMD, g_psInBuf, g_psOutBuf, &rv);
  TEST_ASSERT_EQUAL(0, rv);

  TZIEncodeToDecode(g_psOutBuf);
  rv = TZIDecodeBufF(g_psOutBuf,
                     "%"TZI_DU32 "%"TZI_DARRSPC "%"TZI_DARRSPC,
                     &cmd_id,
                     &audit_nonce, &audit_nonce_len,
                     &audit_string, &audit_string_len);
  TEST_ASSERT_EQUAL(0, rv);

  TEST_ASSERT_EQUAL_STRING("ADD{key=\"key one\"}",
                           audit_string);

  /* execute audited 'add' */

  TZIEncodeBufReInit(g_psInBuf);
  TZIEncodeBufReInit(g_psOutBuf);

  rv = TZIEncodeBufF(g_psInBuf,
                     "%"TZI_EU32 "%"TZI_EARR,
                     cmd_id,
                     audit_token, sizeof(audit_token));
  TEST_ASSERT_EQUAL(0, rv);

  TZIEncodeToDecode(g_psInBuf);
  audited_kv_pal(AKVP_EXECUTE_AUDITED_CMD, g_psInBuf, g_psOutBuf, &rv);
  TZIEncodeToDecode(g_psOutBuf);

  TEST_ASSERT(!rv);
}

void testAuditedAddGetReturnsStoredValue(void)
{
  tz_return_t rv;
  int cmd_id;
  void *audit_nonce;
  size_t audit_nonce_len;
  void *audit_string;
  size_t audit_string_len;
  uint8_t audit_token[] = {0xde, 0xad, 0xbe, 0xef};

  TEST_IGNORE_MESSAGE("test doesn't generate correct audit token yet");

  /* start audited 'add' */
  rv = TZIEncodeBufF(g_psInBuf,
                     "%"TZI_EU32 "%"TZI_ESTR "%"TZI_ESTR,
                     AKVP_DB_ADD, key1, val1);
  TEST_ASSERT_EQUAL(0, rv);

  svc_time_elapsed_us_IgnoreAndReturn(0);
  svc_utpm_rand_block_IgnoreAndReturn(0);

  TZIEncodeToDecode(g_psInBuf);
  audited_kv_pal(AKVP_START_AUDITED_CMD, g_psInBuf, g_psOutBuf, &rv);
  TEST_ASSERT_EQUAL(0, rv);

  TZIEncodeToDecode(g_psOutBuf);
  rv = TZIDecodeBufF(g_psOutBuf,
                     "%"TZI_DU32 "%"TZI_DARRSPC "%"TZI_DARRSPC,
                     &cmd_id,
                     &audit_nonce, &audit_nonce_len,
                     &audit_string, &audit_string_len);
  TEST_ASSERT_EQUAL(0, rv);

  TEST_ASSERT_EQUAL_STRING("ADD{key=\"key one\"}",
                           audit_string);

  /* execute audited 'add' */

  TZIEncodeBufReInit(g_psInBuf);
  TZIEncodeBufReInit(g_psOutBuf);

  rv = TZIEncodeBufF(g_psInBuf,
                     "%"TZI_EU32 "%"TZI_EARR,
                     cmd_id,
                     audit_token, sizeof(audit_token));
  TEST_ASSERT_EQUAL(0, rv);

  TZIEncodeToDecode(g_psInBuf);
  audited_kv_pal(AKVP_EXECUTE_AUDITED_CMD, g_psInBuf, g_psOutBuf, &rv);
  TZIEncodeToDecode(g_psOutBuf);

  TEST_ASSERT_EQUAL(0, rv);

  /* reset marshaling buffers */
  TZIEncodeBufReInit(g_psInBuf);
  TZIEncodeBufReInit(g_psOutBuf);

  /* start audited 'get' */
  rv = TZIEncodeBufF(g_psInBuf,
                     "%"TZI_EU32 "%"TZI_ESTR,
                     AKVP_DB_GET, key1);
  TEST_ASSERT_EQUAL(0, rv);

  svc_time_elapsed_us_IgnoreAndReturn(0);
  svc_utpm_rand_block_IgnoreAndReturn(0);
  TZIEncodeToDecode(g_psInBuf);
  audited_kv_pal(AKVP_START_AUDITED_CMD, g_psInBuf, g_psOutBuf, &rv);
  TEST_ASSERT_EQUAL(0, rv);

  TZIEncodeToDecode(g_psOutBuf);
  rv = TZIDecodeBufF(g_psOutBuf,
                     "%"TZI_DU32 "%"TZI_DARRSPC "%"TZI_DARRSPC,
                     &cmd_id,
                     &audit_nonce, &audit_nonce_len,
                     &audit_string, &audit_string_len);
  TEST_ASSERT_EQUAL(0, rv);

  TEST_ASSERT_EQUAL_STRING("GET{key=\"key one\"}",
                           audit_string);

  /* execute audited 'get' */

  TZIEncodeBufReInit(g_psInBuf);
  TZIEncodeBufReInit(g_psOutBuf);

  rv = TZIEncodeBufF(g_psInBuf,
                     "%"TZI_EU32 "%"TZI_EARR,
                     cmd_id,
                     audit_token, sizeof(audit_token));
  TEST_ASSERT_EQUAL(0, rv);

  TZIEncodeToDecode(g_psInBuf);
  audited_kv_pal(AKVP_EXECUTE_AUDITED_CMD, g_psInBuf, g_psOutBuf, &rv);
  TZIEncodeToDecode(g_psOutBuf);

  {
    char *returned_val;
    rv = TZIDecodeBufF(g_psOutBuf,
                       "%"TZI_DARRSPC_NOLEN,
                       &returned_val);
    TEST_ASSERT(!rv);
    TEST_ASSERT_EQUAL_STRING(val1, returned_val);
  }
}
