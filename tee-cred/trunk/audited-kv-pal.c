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

#include <tz.h>
#include <tzmarshal.h>

#include <string.h>
#include <malloc.h>
#include <assert.h>
#include <stdarg.h>

#define FREE_AND_NULL(x) do { free(x) ; x=NULL; } while(0)

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

typedef struct {
  char *key;
  char *val;
} akvp_db_add_cont_t;

void akvp_db_add_release(void* vcont)
{
  akvp_db_add_cont_t *cont = (akvp_db_add_cont_t*)vcont;
  FREE_AND_NULL(cont->key);
  FREE_AND_NULL(cont->val);
}

tz_return_t akvp_db_add_begin_marshal(char **audit_string,
                                      void **vcont,
                                      struct tzi_encode_buffer_t *psInBuf)
{
  char *key, *val;
  size_t key_len, val_len;

  key = TZIDecodeArraySpace(psInBuf, &key_len);
  val = TZIDecodeArraySpace(psInBuf, &val_len);

  if (TZIDecodeGetError(psInBuf)) {
    return TZIDecodeGetError(psInBuf);
  }
  if (key[key_len-1] != '\0'
      || val[val_len-1] != '\0') {
    return TZ_ERROR_ILLEGAL_ARGUMENT;
  }

  return akvp_db_add_begin(audit_string, vcont, key, val);
}


tz_return_t akvp_db_add_begin(char **audit_string,
                              void **vcont,
                              const char* key,
                              const char* val)
{
  akvp_db_add_cont_t **cont = (akvp_db_add_cont_t**)vcont;

  *cont = malloc(sizeof(**cont));
  if(!*cont) {
    return TZ_ERROR_MEMORY;
  }

  (*cont)->key = strcpy_mallocd(key);
  (*cont)->val = strcpy_mallocd(val);
  *audit_string =
    sprintf_mallocd("ADD{key=\"%s\"}", key);

  if (!(*cont)->key
      || !(*cont)->val
      || !*audit_string) {
    FREE_AND_NULL((*cont)->key);
    FREE_AND_NULL((*cont)->val);
    FREE_AND_NULL(*cont);
    FREE_AND_NULL(*audit_string);
    return TZ_ERROR_MEMORY;
  }

  return TZ_SUCCESS;
}

tz_return_t akvp_db_add_execute(void* vcont)
{
  /* akvp_db_add_cont_t *cont = (akvp_db_add_cont_t*)vcont; */
  return TZ_ERROR_NOT_IMPLEMENTED;
}
