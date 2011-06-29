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

#include "audited-kv-pal.h"
#include "audited-kv-pal-fns.h"

#include <string.h>
#include <malloc.h>
#include <assert.h>
#include <stdarg.h>

#define free_and_null(x) do { free(x) ; x=NULL; } while(0)

static char* strcpy_mallocd(const char *src)
{
  size_t len = strlen(src)+1;
  char *rv = malloc(len);
  if(!rv) {
    return NULL;
  }
  strcpy(rv, src);
  return rv;
}

char* sprintf_mallocd(const char *format, ...)
{
  va_list argp1;
  va_list argp2;
  size_t sz, sz2;
  char *rv=NULL;

  va_start(argp1, format);
  va_copy(argp2, argp1);

  sz = 1+vsnprintf(NULL, 0, format, argp1);
  rv = malloc(sz);
  if (!rv)
    goto out;
  sz2 = vsnprintf(rv, sz, format, argp2);
  assert(sz2 == (sz-1));

 out:
  va_end(argp1);
  va_end(argp2);
  return rv;
}

static struct {
  bool valid;
  char *key;
  char *val;
} db_add_saved = {
  .valid=false,
  .key=NULL,
  .val=NULL,
};

void akvp_db_add_release(void)
{
  free_and_null(db_add_saved.key);
  free_and_null(db_add_saved.val);
  db_add_saved.valid=false;
}

tz_return_t akvp_db_add_begin(char **audit_string,
                              const char* key,
                              const char* val)
{
  return TZ_ERROR_NOT_IMPLEMENTED;
  assert(!db_add_saved.valid);

  db_add_saved.key = strcpy_mallocd(key);
  db_add_saved.val = strcpy_mallocd(val);
  *audit_string =
    sprintf_mallocd("ADD{key=\"%s\"}", key);

  if (!db_add_saved.key
      || !db_add_saved.val
      || !*audit_string) {
    free_and_null(db_add_saved.key);
    free_and_null(db_add_saved.val);
    free_and_null(*audit_string);
    return TZ_ERROR_MEMORY;
  }

  db_add_saved.valid = true;

  return TZ_SUCCESS;
}

tz_return_t akvp_db_add_execute(void)
{
  assert(db_add_saved.valid);
  return TZ_ERROR_NOT_IMPLEMENTED;
}

