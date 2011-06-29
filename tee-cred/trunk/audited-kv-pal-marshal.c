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

#include <assert.h>
#include <tzmarshal.h>
#include <string.h>

typedef tz_return_t (audited_execute_fn)(void *, struct tzi_encode_buffer_t *);
typedef void (audited_release_fn)(void *);

typedef struct {
  char *audit_string;
  void *cont;
  audited_execute_fn *execute_fn;
  audited_release_fn *release_fn;
  uint64_t epoch_nonce;
  uint64_t epoch_offset;
  void *audit_nonce;
  size_t audit_nonce_len;
} pending_cmd_t;

#define MAX_PENDING 100
static pending_cmd_t pending_cmds[MAX_PENDING];
static int num_pending=0;

static int get_free_pending_id()
{
  /* FIXME: handle multiple pending cmds */
  assert(num_pending == 0);
  num_pending++;
  return 0;
}

/* static void release_pending_cmd_id(int i) */
/* { */
/*   pending_cmd_t *cmd; */
/*   /\* FIXME: handle multiple pending cmds *\/ */
/*   assert(i==0); */
/*   assert(num_pending == 1); */

/*   cmd = &pending_cmds[i]; */
/*   free(cmd->audit_string); */
/*   if(cmd->release_fn && cmd->cont) { */
/*     cmd->release_fn(cmd->cont); */
/*   } */
/*   free(cmd->audit_nonce); */

/*   num_pending--; */
/* } */

static int save_pending_cmd(char *audit_string, void *cont, audited_execute_fn execute_fn, audited_release_fn release_fn)
{
  int cmd_id = get_free_pending_id();
  uint64_t epoch_nonce, epoch_offset;
  void *audit_nonce;
  size_t audit_nonce_len;
  int rv;

  rv = svc_time_elapsed_us(&epoch_nonce, &epoch_offset);
  if(rv) {
    return -1;
  }

  audit_nonce_len = 256;
  audit_nonce = malloc(audit_nonce_len);
  if(!audit_nonce) {
    return -1;
  }
  rv = svc_utpm_rand_block(audit_nonce, audit_nonce_len);

  pending_cmds[cmd_id] = (pending_cmd_t) {
    .audit_string = audit_string,
    .cont = cont,
    .execute_fn = execute_fn,
    .release_fn = release_fn,
    .epoch_nonce = epoch_nonce,
    .epoch_offset = epoch_offset,
    .audit_nonce = audit_nonce,
    .audit_nonce_len = audit_nonce_len,
  };
  return cmd_id;
}

void audited_kv_pal(uint32_t uiCommand, struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv)
{
  switch(uiCommand) {
  case AKVP_START_AUDITED_CMD:
    {
      uint32_t audited_cmd = TZIDecodeUint32(psInBuf);
      char *audit_string=NULL;
      void *cont=NULL;
      audited_execute_fn *execute_fn=NULL;
      audited_release_fn *release_fn=NULL;
      int pending_cmd_id;
      pending_cmd_t *pending_cmd=NULL;

      if(TZIDecodeGetError(psInBuf)) {
        *puiRv = TZIDecodeGetError(psInBuf);
        return;
      }

      switch(audited_cmd) {
      case AKVP_DB_ADD:
        *puiRv = akvp_db_add_begin_marshal(&audit_string, cont, psInBuf);
        execute_fn = akvp_db_add_execute;
        release_fn = akvp_db_add_release;
        break;
      case AKVP_DB_GET:
        *puiRv = akvp_db_get_begin_marshal(&audit_string, cont, psInBuf);
        execute_fn = akvp_db_get_execute;
        release_fn = akvp_db_get_release;
        break;
      default:
        *puiRv = AKV_EBADAUDITEDCMD;
        break;
      }

      if (*puiRv != TZ_SUCCESS) {
        free(audit_string);
        if(release_fn && cont) {
          release_fn(cont);
        }
        /* XXX release cont? */
        return;
      }

      /* returns:
         uint32 pending command handle
         array  audit-nonce (binary data)
         array  audit-string (null-terminated string)
      */
      pending_cmd_id = save_pending_cmd(audit_string, cont, execute_fn, release_fn);
      pending_cmd = &pending_cmds[pending_cmd_id];
      TZIEncodeUint32(psOutBuf, pending_cmd_id);
      TZIEncodeArray(psOutBuf, pending_cmd->audit_nonce, pending_cmd->audit_nonce_len);
      TZIEncodeArray(psOutBuf, audit_string, strlen(audit_string)+1);
    }
    break;
  case AKVP_EXECUTE_AUDITED_CMD:
    {
      *puiRv = TZ_ERROR_NOT_IMPLEMENTED;
    }
    break;
  default:
    *puiRv = TZ_ERROR_NOT_IMPLEMENTED;
    break;
  }
}
