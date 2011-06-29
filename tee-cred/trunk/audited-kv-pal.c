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

static void free_and_null(void **ptr)
{
  free(*ptr);
  *ptr = NULL;
}

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

static struct {
  bool valid;
  const char *key;
  const char *val;
} db_add_saved = {
  .valid=false,
  .key=NULL,
  .val=NULL,
};

void akvp_db_add_release(void)
{
  free_and_null((void**)&db_add_saved.key);
  free_and_null((void**)&db_add_saved.val);
  db_add_saved.valid=false;
}

tz_return_t akvp_db_add_begin(char *audit_string,
                              size_t *audit_string_sz,
                              const char* key,
                              const char* val)
{
  return TZ_ERROR_NOT_IMPLEMENTED;
  assert(!db_add_saved.valid);

  db_add_saved.key = strcpy_mallocd(key);
  db_add_saved.val = strcpy_mallocd(val);
  if (!db_add_saved.key || !db_add_saved.val) {
    akvp_db_add_release();
    return TZ_ERROR_MEMORY;
  }
  
  {
    size_t bufsz=*audit_string_sz;
    /* FIXME escape quotes, etc. */
    *audit_string_sz = 0;
    *audit_string_sz += snprintf(audit_string,
                                 bufsz,
                                 "ADD{key=\"%s\"}",
                                 key);
    *audit_string_sz += 1; /* null */
    if(*audit_string_sz > bufsz) {
      akvp_db_add_release();
      return TZ_ERROR_SHORT_BUFFER;
    }
  }
  

  return TZ_SUCCESS;
}

tz_return_t akvp_db_add_execute(void)
{
  assert(db_add_saved.valid);
  return TZ_ERROR_NOT_IMPLEMENTED;
}

