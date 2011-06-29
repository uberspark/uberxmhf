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

typedef tz_return_t (audited_execute_fn)(void *, struct tzi_encode_buffer_t *);
typedef void (audited_release_fn)(void *);

typedef struct {
  char *audit_string;
  void *cont;
  audited_execute_fn execute_fn;
  audited_release_fn release_fn;
  uint64_t epoch_nonce;
  uint64_t epoch_offset;
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

static void release_pending_id(int i)
{
  /* FIXME: handle multiple pending cmds */
  assert(i==0);
  assert(num_pending == 1);
  num_pending--;
}

static int save_pending_cmd(char *audit_string, void *cont, audited_execute_fn execute_fn, audited_release_fn release_fn)
{
  int cmd_id = get_free_pending_id();
  pending_cmd_t *cmd = &pending_cmds[cmd_id];
  uint64_t epoch_nonce, epoch_offset;
  int rv;

  rv = svc_time_elapsed_us(&epoch_nonce, &epoch_offset);
  if(rv) {
    return -1;
  }

  pending_cmds[cmd_id] = (pending_cmd_t) {
    .audit_string = audit_string,
    .cont = cont,
    .execute_fn = execute_fn,
    .release_fn = release_fn,
    .epoch_nonce = epoch_nonce,
    .epoch_offset = epoch_offset,
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

      switch(audited_cmd) {
      case AKVP_DB_ADD:
        *puiRv = akvp_db_add_begin(&audit_string, cont, psInBuf);
        break;
      case AKVP_DB_GET:
        *puiRv = akvp_db_get_begin(&audit_string, cont, psInBuf);
        break;
      default:
        *puiRv = AKV_EBADAUDITEDCMD;
        break;
      }

      if (*puiRv != TZ_SUCCESS) {
        free(audit_string);
        /* XXX release cont? */
        return;
      }
      TZIEncodeArray(psOutBuf, audit_string, strlen(audit_string)+1);
      free(audit_string);
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
