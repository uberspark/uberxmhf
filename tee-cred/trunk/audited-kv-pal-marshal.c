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

#include <tee-sdk/tzmarshal.h>

#include "audited-kv-pal.h"
#include "audited-kv-pal-fns.h"
#include "audited.h"

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

 out:
  return rv;
}

akv_err_t akvp_audited_start_unmarshal(struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf)
{
  uint32_t audited_cmd;
  char *audit_string=NULL;
  uint32_t pending_cmd_id;
  akv_err_t rv;
  void *audit_nonce;
  uint32_t audit_nonce_len;

  audited_cmd = TZIDecodeUint32(psInBuf);

  if(TZIDecodeGetError(psInBuf)) {
    rv = AKV_EDECODE;
    goto out;
  }

  rv = audited_start_cmd(audited_cmd,
                         psInBuf,
                         &pending_cmd_id,
                         &audit_string,
                         &audit_nonce,
                         &audit_nonce_len);

  TZIEncodeUint32(psOutBuf, pending_cmd_id);
  TZIEncodeArray(psOutBuf, audit_nonce, audit_nonce_len);
  TZIEncodeArray(psOutBuf, audit_string, strlen(audit_string)+1);

 out:
  return rv;
}

akv_err_t akvp_audited_execute_unmarshal(struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf)
{
  void *audit_token;
  uint32_t audit_token_len;
  uint32_t cmd_id;
  akv_err_t rv;

  cmd_id = TZIDecodeUint32(psInBuf);
  audit_token = TZIDecodeArraySpace(psInBuf, &audit_token_len);
  if (TZIDecodeGetError(psInBuf)) {
    rv = AKV_EDECODE;
    goto out;
  }

  rv = audited_execute_cmd(cmd_id, audit_token, audit_token_len, psOutBuf);

 out:
  return rv;
}
