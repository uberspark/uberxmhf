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

/* typedef struct { */
/*   audited_begin_fn *begin; */
/*   audited_execute_fn *execute; */
/*   audited_release_fn *release; */
/* } audited_cmd_t; */
/* audited_cmd_t audited_cmds[] = { */
/*   [AKVP_DB_ADD] = { */
/*     .begin=akvp_db_add_begin_marshal, */
/*     .execute=akvp_db_add_execute, */
/*     .release=akvp_db_add_release, */
/*   }, */
/*   [AKVP_DB_GET] = { */
/*     .begin=akvp_db_get_begin_marshal, */
/*     .execute=akvp_db_get_execute, */
/*     .release=akvp_db_get_release, */
/*   }, */
/* }; */

char end[10*4096]; /* define the end of the data segment and some
                      buffer spacefor libnosys's sbrk */

void audited_kv_pal(uint32_t uiCommand, struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv)
{
  static bool did_init = false;

  switch(uiCommand) {
  case AKVP_INIT:
    {
      const char *audit_pub_pem;
      uint32_t audit_pub_len;

      if (TZIDecodeBufF(psInBuf, "%"TZI_DARRSPC, &audit_pub_pem, &audit_pub_len)) {
        *puiRv=AKV_EDECODE;
        break;
      }
      if (audit_pub_pem[audit_pub_len-1] != '\0') {
        *puiRv=AKV_EPARAM;
        break;
      }
      
      *puiRv = akvp_init(audit_pub_pem);
      if(*puiRv == AKV_ENONE)
        did_init=true;
    }
    break;

  case AKVP_START_AUDITED_CMD:
    {
      uint32_t audited_cmd = TZIDecodeUint32(psInBuf);
      char *audit_string=NULL;
      void *cont=NULL;
      audited_execute_fn *execute_fn=NULL;
      audited_release_fn *release_fn=NULL;
      int pending_cmd_id;
      audited_pending_cmd_t *pending_cmd=NULL;

      if(!did_init) {
        *puiRv = AKV_EBADSTATE;
        return;
      }

      if(TZIDecodeGetError(psInBuf)) {
        *puiRv = AKV_EDECODE;
        return;
      }

      switch(audited_cmd) {
      case AKVP_DB_ADD:
        *puiRv = akvp_db_add_begin_marshal(&audit_string, &cont, psInBuf);
        execute_fn = akvp_db_add_execute;
        release_fn = akvp_db_add_release;
        break;
      case AKVP_DB_GET:
        *puiRv = akvp_db_get_begin_marshal(&audit_string, &cont, psInBuf);
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
      pending_cmd_id = audited_save_pending_cmd(audit_string, cont, execute_fn, release_fn);
      pending_cmd = audited_pending_cmd_of_id(pending_cmd_id);
      TZIEncodeUint32(psOutBuf, pending_cmd_id);
      TZIEncodeArray(psOutBuf, pending_cmd->audit_nonce, pending_cmd->audit_nonce_len);
      TZIEncodeArray(psOutBuf, audit_string, strlen(audit_string)+1);
    }
    break;
  case AKVP_EXECUTE_AUDITED_CMD:
    {
      void *audit_token;
      uint32_t audit_token_len;
      int cmd_id;
      audited_pending_cmd_t *cmd;

      if(!did_init) {
        *puiRv = AKV_EBADSTATE;
        return;
      }

      cmd_id = TZIDecodeUint32(psInBuf);
      audit_token = TZIDecodeArraySpace(psInBuf, &audit_token_len);

      if (TZIDecodeGetError(psInBuf)) {
        *puiRv = AKV_EDECODE;
        return;
      }

      if (!(cmd = audited_pending_cmd_of_id(cmd_id))) {
        *puiRv = AKV_EBADCMDHANDLE;
        return;
      }

      if (audited_check_cmd_auth(cmd,
                                 audit_token,
                                 audit_token_len)) {
        *puiRv = AKV_EBADAUTH;
        return;
      }

      *puiRv = cmd->execute_fn(cmd->cont, psOutBuf);
      audited_release_pending_cmd_id(cmd_id);
      return;
    }
    break;
  default:
    *puiRv = AKV_EBADCMD;
    break;
  }
}
