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

#include <string.h>
#include <tzmarshal.h>

#include <unity.h>
#include "audited-kv-pal-fns.h"
#include "audited-kv-errs.h"

static const char * key1 = "key one";
static const size_t key1_len = 8;
static const char * val1 = "value one";
static const size_t val1_len = 10;

static tzi_encode_buffer_t *psInBuf, *psOutBuf;


void setUp(void)
{
  akvp_init();
  psInBuf = malloc(1000);
  TZIEncodeBufInit(psInBuf, 1000);

  psOutBuf = malloc(1000);
  TZIEncodeBufInit(psOutBuf, 1000);
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
  void *cont;
  tz_return_t rv;

  rv = akvp_db_add_begin(&audit_string,
                         &cont,
                         key1, key1_len,
                         val1, val1_len);
  TEST_ASSERT(rv == TZ_SUCCESS);
  TEST_ASSERT_NOT_NULL(audit_string);
  TEST_ASSERT_EQUAL_STRING("ADD{key=\"key one\"}",
                           audit_string);
  free(audit_string);
  akvp_db_add_release(cont);
}

void test_akvp_db_add_succeeds()
{
  char *audit_string;
  void *cont;
  tz_return_t rv;

  rv = akvp_db_add_begin(&audit_string,
                         &cont,
                         key1, key1_len,
                         val1, val1_len);
  TEST_ASSERT(rv == TZ_SUCCESS);
  free(audit_string);

  rv = akvp_db_add_execute(cont, psOutBuf);
  TEST_ASSERT(!rv);
  akvp_db_add_release(cont);
}

void test_akvp_db_add_duplicate_fails()
{
  char *audit_string;
  void *cont;
  tz_return_t rv;

  rv = akvp_db_add_begin(&audit_string,
                         &cont,
                         key1, key1_len,
                         val1, val1_len);
  TEST_ASSERT(rv == TZ_SUCCESS);
  free(audit_string);

  rv = akvp_db_add_execute(cont, psOutBuf);
  TEST_ASSERT(!rv);
  rv = akvp_db_add_execute(cont, psOutBuf);
  TEST_ASSERT_EQUAL(AKV_EEXISTS, rv);
  akvp_db_add_release(cont);
}
