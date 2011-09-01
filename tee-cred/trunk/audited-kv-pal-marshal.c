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

#include <assert.h>
#include <string.h>

#include <tee-sdk/tzmarshal.h>

#include "audited-kv-pal.h"
#include "audited-kv-pal-fns.h"
#include "audited.h"

typedef struct {
  audited_begin_fn *begin;
  audited_execute_fn *execute;
  audited_release_fn *release;
} audited_cmd_t;

audited_cmd_t audited_cmds[] = {
  [AKVP_DB_ADD] = {
    .begin=akvp_db_add_begin_marshal,
    .execute=akvp_db_add_execute,
    .release=akvp_db_add_release,
  },
  [AKVP_DB_GET] = {
    .begin=akvp_db_get_begin_marshal,
    .execute=akvp_db_get_execute,
    .release=akvp_db_get_release,
  },
};
size_t audited_cmds_num = sizeof(audited_cmds)/sizeof(audited_cmd_t);

char end[10*4096]; /* define the end of the data segment and some
                      buffer spacefor libnosys's sbrk */

static bool did_init = false;

static akv_err_t akvp_init_unmarshal(struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf);
static akv_err_t akvp_audited_start_unmarshal(struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf);
static akv_err_t akvp_audited_execute_unmarshal(struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf);

void audited_kv_pal(uint32_t uiCommand, struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv)
{
  switch(uiCommand) {
  case AKVP_INIT:
    *puiRv = akvp_init_unmarshal(psInBuf, psOutBuf);
    break;

  case AKVP_START_AUDITED_CMD:
    *puiRv = akvp_audited_start_unmarshal(psInBuf, psOutBuf);
    break;

  case AKVP_EXECUTE_AUDITED_CMD:
    *puiRv = akvp_audited_execute_unmarshal(psInBuf, psOutBuf);
    break;
  default:
    *puiRv = AKV_EBADCMD;
    break;
  }
}

akv_err_t akvp_init_unmarshal(struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf)
{
  const char *audit_pub_pem;
  uint32_t audit_pub_len;
  akv_err_t rv;

  if (TZIDecodeBufF(psInBuf, "%"TZI_DARRSPC, &audit_pub_pem, &audit_pub_len)) {
    rv=AKV_EDECODE;
    goto out;
  }

  if (audit_pub_pem[audit_pub_len-1] != '\0') {
    rv=AKV_EPARAM;
    goto out;
  }
      
  rv = akvp_init(audit_pub_pem);

  if(rv == AKV_ENONE)
    did_init=true;
 out:
  return rv;
}

akv_err_t akvp_audited_start_unmarshal(struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf)
{
  uint32_t audited_cmd;
  char *audit_string=NULL;
  void *cont=NULL;
  audited_execute_fn *execute_fn=NULL;
  audited_release_fn *release_fn=NULL;
  int pending_cmd_id;
  audited_pending_cmd_t *pending_cmd=NULL;
  akv_err_t rv;

  if(!did_init) {
    rv = AKV_EBADSTATE;
    goto out;
  }

  audited_cmd = TZIDecodeUint32(psInBuf);

  if(TZIDecodeGetError(psInBuf)) {
    rv = AKV_EDECODE;
    goto out;
  }

  if (audited_cmd >= audited_cmds_num
      || !audited_cmds[audited_cmd].begin) {
    rv = AKV_EBADAUDITEDCMD;
    goto out;
  }

  rv = audited_cmds[audited_cmd].begin(&audit_string, &cont, psInBuf);
  execute_fn = audited_cmds[audited_cmd].execute;
  release_fn = audited_cmds[audited_cmd].release;

  if (rv != TZ_SUCCESS) {
    free(audit_string);
    if(release_fn && cont) {
      release_fn(cont);
    }
    /* XXX release cont? */
    goto out;
  }

  /* returns:
     uint32 pending command handle
     array  audit-nonce (binary data)
     array  audit-string (null-terminated string)
  */
  pending_cmd_id = audited_save_pending_cmd(audit_string, cont, execute_fn, release_fn);
  pending_cmd = audited_pending_cmd_of_id(pending_cmd_id);
  TZIEncodeUint32(psOutBuf, pending_cmd_id);
  TZIEncodeArray(psOutBuf, pending_cmd->audit_nonce, pending_cmd->audit_nonce_len);
  TZIEncodeArray(psOutBuf, audit_string, strlen(audit_string)+1);

 out:
  return rv;
}

akv_err_t akvp_audited_execute_unmarshal(struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf)
{
  void *audit_token;
  uint32_t audit_token_len;
  int cmd_id;
  audited_pending_cmd_t *cmd;
  akv_err_t rv;

  if(!did_init) {
    rv = AKV_EBADSTATE;
    goto out;
  }

  cmd_id = TZIDecodeUint32(psInBuf);
  audit_token = TZIDecodeArraySpace(psInBuf, &audit_token_len);

  if (TZIDecodeGetError(psInBuf)) {
    rv = AKV_EDECODE;
    goto out;
  }

  if (!(cmd = audited_pending_cmd_of_id(cmd_id))) {
    rv = AKV_EBADCMDHANDLE;
    goto out;
  }

  if (audited_check_cmd_auth(cmd,
                             audit_token,
                             audit_token_len)) {
    rv = AKV_EBADAUTH;
    goto out;
  }

  rv = cmd->execute_fn(cmd->cont, psOutBuf);

  audited_release_pending_cmd_id(cmd_id);
 out:
  return rv;
}
