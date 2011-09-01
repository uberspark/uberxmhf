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
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#include <tee-sdk/svcapi.h>

#include <openssl/bio.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/engine.h>
#include <openssl/sha.h>

#include "audited.h"

static audited_pending_cmd_t pending_cmds[AUDITED_MAX_PENDING];
static int num_pending=0;
static RSA* audit_pub_key=NULL;

static bool did_init=false;

static int get_free_pending_id()
{
  /* FIXME: handle multiple pending cmds */
  assert(num_pending == 0);
  num_pending++;
  return 0;
}

audited_err_t audited_init(const char* audit_server_pub_pem)
{
  BIO *mem;

  mem = BIO_new_mem_buf((char*)audit_server_pub_pem, -1);
  audit_pub_key =
    PEM_read_bio_RSA_PUBKEY(mem, NULL, NULL, NULL);
  if (!audit_pub_key) {
    ERR_print_errors_fp(stderr);
    return AUDITED_EBADKEY;
  }
  did_init=true;
  return AUDITED_ENONE;
}

void audited_release_pending_cmd_id(int i)
{
  audited_pending_cmd_t *cmd;
  /* FIXME: handle multiple pending cmds */
  assert(i==0);
  assert(num_pending == 1);

  cmd = &pending_cmds[i];
  free(cmd->audit_string);
  if(cmd->fns && cmd->fns->release_req && cmd->req) {
    cmd->fns->release_req(cmd->req);
  }
  free(cmd->audit_nonce);

  num_pending--;
}

audited_pending_cmd_t* audited_pending_cmd_of_id(int i)
{
  assert(i == 0 && num_pending == 1);
  return &pending_cmds[i];
}

int audited_save_pending_cmd(audited_cmd_t *fns, void *req, char *audit_string)
{
  int cmd_id = get_free_pending_id();
  uint64_t epoch_nonce, epoch_offset;
  void *audit_nonce;
  size_t audit_nonce_len;
  int rv;

  assert(fns);
  assert(audit_string);

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

  pending_cmds[cmd_id] = (audited_pending_cmd_t) {
    .audit_string = audit_string,
    .req = req,
    .fns = fns,
    .epoch_nonce = epoch_nonce,
    .epoch_offset = epoch_offset,
    .audit_nonce = audit_nonce,
    .audit_nonce_len = audit_nonce_len,
  };
  return cmd_id;
}

audited_err_t audited_check_cmd_auth(audited_pending_cmd_t *cmd, const void* audit_token, size_t audit_token_len)
{
  uint64_t epoch_nonce, epoch_offset;
  int svc_rv;
  audited_err_t rv=AUDITED_ENONE;
  SHA256_CTX sha256_ctx;
  uint8_t digest[SHA256_DIGEST_LENGTH];

  /* check time first, in case signature verification time is significant */
  svc_rv = svc_time_elapsed_us(&epoch_nonce, &epoch_offset);
  if(svc_rv 
     || epoch_nonce != cmd->epoch_nonce
     || (epoch_offset - cmd->epoch_offset) > AUDITED_TIMEOUT_US) {
    rv = AUDITED_ETIMEOUT;
    goto out;
  }

  /* check signature */

  /* compute digest of expected message */
  if (!SHA256_Init(&sha256_ctx)
      || !SHA256_Update(&sha256_ctx,
                        cmd->audit_nonce,
                        cmd->audit_nonce_len)
      || !SHA256_Update(&sha256_ctx,
                        cmd->audit_string,
                        strlen(cmd->audit_string)) /* null not included */
      || !SHA256_Final(&digest[0], &sha256_ctx)) {
    ERR_print_errors_fp(stderr);
    rv = AUDITED_ECRYPTO;
    goto out;
  }
  if(!RSA_verify(NID_sha256,
                 digest, SHA256_DIGEST_LENGTH,
                 (unsigned char*)audit_token, audit_token_len,
                 audit_pub_key)) {
    rv = AUDITED_EBADSIG;
    goto out;
  }

 out:
  return rv;
}

audited_err_t audited_start_cmd(uint32_t audited_cmd,
                                tzi_encode_buffer_t *psInBuf,
                                uint32_t *pending_cmd_id,
                                char **audit_string,
                                void **audit_nonce,
                                uint32_t *audit_nonce_len)
{
  audited_err_t rv;
  void *req=NULL;
  audited_cmd_t *fns=NULL;

  *audit_string=NULL;
  *audit_nonce=NULL;

  if(!did_init) {
    rv = AUDITED_EBADSTATE;
    goto out;
  }

  if (audited_cmd >= audited_cmds_num) {
    rv = AUDITED_EBADAUDITEDCMD;
    goto out;
  }
  fns = &audited_cmds[audited_cmd];
  assert(fns);

  assert(fns->decode_req);
  rv = fns->decode_req(&req, psInBuf, psInBuf->uiSize + sizeof(tzi_encode_buffer_t));
  if (!rv) {
    rv = AUDITED_EDECODE;
    goto out;
  }

  assert(fns->audit_string);
  rv = fns->audit_string(req, audit_string);
  if (rv) {
    rv = AUDITED_EAUDITSTRING;
    goto out;
  }

  *pending_cmd_id = audited_save_pending_cmd(fns, req, *audit_string);
  if (*pending_cmd_id < 0) {
    rv = AUDITED_ESAVE;
    goto out;
  }

  *audit_string = pending_cmds[*pending_cmd_id].audit_string;
  *audit_nonce = pending_cmds[*pending_cmd_id].audit_nonce;
  *audit_nonce_len = pending_cmds[*pending_cmd_id].audit_nonce_len;

 out:
  if (rv) {
    free(*audit_string);
    *audit_string=NULL;
    free(*audit_nonce);
    *audit_nonce=NULL;
    if(fns && fns->release_req && req) {
      fns->release_req(req);
    }
    req = NULL;
  }
  return rv;
}

audited_err_t audited_execute_cmd(uint32_t cmd_id,
                                  void *audit_token,
                                  size_t audit_token_len,
                                  tzi_encode_buffer_t *psOutBuf)
{
  audited_err_t rv;
  audited_pending_cmd_t *cmd;
  void *res=NULL;
  void *outbuf;
  size_t outbuf_len;

  if(!did_init) {
    rv = AUDITED_EBADSTATE;
    goto out;
  }

  if (!(cmd = audited_pending_cmd_of_id(cmd_id))) {
    rv = AUDITED_EBADCMDHANDLE;
    goto out;
  }

  rv = audited_check_cmd_auth(cmd,
                              audit_token,
                              audit_token_len);
  if (rv) {
    goto out;
  }

  assert(cmd->fns);

  assert(cmd->fns->execute);
  rv = cmd->fns->execute(cmd->req, res);

  assert(cmd->fns->encode_res_maxlen);
  outbuf_len = cmd->fns->encode_res_maxlen(res);
  outbuf = TZIEncodeArraySpace(psOutBuf, outbuf_len);
  assert(cmd->fns->encode_res);
  rv = cmd->fns->encode_res(res, outbuf, &outbuf_len);

  audited_release_pending_cmd_id(cmd_id);

 out:
  return rv;
}
