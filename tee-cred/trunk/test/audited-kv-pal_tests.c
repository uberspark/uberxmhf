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

#include <string.h>
#include <tzmarshal.h>

#include <unity.h>
#include "audited-kv-pal-fns.h"
#include "audited-kv-errs.h"

static const char * key1 = "key one";
static const size_t key1_len = 8;
static const char * val1 = "value one";
static const size_t val1_len = 10;
static akvp_db_add_req_t req;

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

static tzi_encode_buffer_t *psInBuf, *psOutBuf;


void setUp(void)
{
  tz_return_t rv;
  rv = akvp_init(audit_pub);
  TEST_ASSERT(!rv);

  psInBuf = malloc(1000);
  TZIEncodeBufInit(psInBuf, 1000);

  psOutBuf = malloc(1000);
  TZIEncodeBufInit(psOutBuf, 1000);

  req =
    (akvp_db_add_req_t) {
    .key = (char*)key1,
    .key_len = key1_len,
    .val = (char*)val1,
    .val_len = val1_len,
  };

}

void tearDown(void)
{
  akvp_release();
  free(psInBuf);
  free(psOutBuf);
}

void test_akvp_db_add_begin_gives_expected_audit_string()
{
  char *audit_string;
  tz_return_t rv;
  rv = akvp_db_add_audit_string(&req,
                                &audit_string);
  TEST_ASSERT(rv == TZ_SUCCESS);
  TEST_ASSERT_NOT_NULL(audit_string);
  TEST_ASSERT_EQUAL_STRING("ADD{key=\"key one\"}",
                           audit_string);
  free(audit_string);
}

void test_akvp_db_add_succeeds()
{
  void *res;
  tz_return_t rv;

  rv = akvp_db_add_execute(&req, &res);
  TEST_ASSERT(rv == TZ_SUCCESS);
  akvp_db_add_release_res(res);
}

void test_akvp_db_add_duplicate_fails()
{
  void *res;
  tz_return_t rv;

  rv = akvp_db_add_execute(&req, &res);
  TEST_ASSERT(rv == TZ_SUCCESS);
  akvp_db_add_release_res(res);

  rv = akvp_db_add_execute(&req, &res);
  TEST_ASSERT(rv);
  akvp_db_add_release_res(res);
}

void test_akvp_db_get_begin_gives_expected_audit_string()
{
  char *audit_string;
  void *cont;
  tz_return_t rv;

  rv = akvp_db_get_begin(&audit_string,
                         &cont,
                         key1, key1_len);
  TEST_ASSERT(rv == TZ_SUCCESS);
  TEST_ASSERT_NOT_NULL(audit_string);
  TEST_ASSERT_EQUAL_STRING("GET{key=\"key one\"}",
                           audit_string);
  free(audit_string);
  akvp_db_get_release(cont);
}

void test_akvp_db_get_execute_empty_fails()
{
  char *audit_string;
  void *cont;
  tz_return_t rv;

  rv = akvp_db_get_begin(&audit_string,
                         &cont,
                         key1, key1_len);
  free(audit_string);
  TEST_ASSERT(rv == TZ_SUCCESS);

  rv = akvp_db_get_execute(cont, psOutBuf);
  TEST_ASSERT_EQUAL(AKV_ENOTFOUND, rv);
  akvp_db_get_release(cont);
}

void test_akvp_db_get_execute_existing_succeeds(void)
{
  char *audit_string;
  void *cont;
  void *val;
  size_t val_len;
  void *add_res;

  TEST_ASSERT(!akvp_db_add_execute(&req, &add_res));
  akvp_db_add_release_res(add_res);

  TEST_ASSERT(!akvp_db_get_begin(&audit_string,
                                 &cont,
                                 key1, key1_len));
  free(audit_string);
  TEST_ASSERT(!akvp_db_get_execute(cont, psOutBuf));
  akvp_db_get_release(cont);

  TZIEncodeToDecode(psOutBuf);
  val = TZIDecodeArraySpace(psOutBuf, &val_len);
  TEST_ASSERT_EQUAL(0, TZIDecodeGetError(psOutBuf));
  TEST_ASSERT_EQUAL(val1_len, val_len);
  TEST_ASSERT_EQUAL_STRING(val1, val);
}
