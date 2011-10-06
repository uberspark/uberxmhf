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

#include "proto-gend/audited.pb-c.h"
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

static void clone_mem_bio(BIO *bio, void **buf, size_t *buflen)
{
  char *internal_buf;
  size_t len;

  *buf=NULL;

  len = BIO_get_mem_data(bio, &internal_buf);
  if (!internal_buf) {
    return;
  }

  if(buflen) {
    *buflen=len;
  }

  *buf = malloc(len+1); /* always allocate an extra space for a null
                           character, but leave it to caller to
                           actually set it if needed */
  if(!*buf) {
    return;
  }

  memcpy(*buf, internal_buf, len);
  return;
}

audited_err_t audited_init(const char* audit_server_pub_pem)
{
  audited_err_t rv=0;
  BIO *mem;
  did_init=false;

  if(audit_pub_key) {
    RSA_free(audit_pub_key);
    audit_pub_key=NULL;
  }

  mem = BIO_new_mem_buf((char*)audit_server_pub_pem, -1);
  if(!mem) {
    rv=AUDITED_ECRYPTO;
    goto out;
  }

  audit_pub_key =
    PEM_read_bio_RSA_PUBKEY(mem, NULL, NULL, NULL);
  if (!audit_pub_key) {
    ERR_print_errors_fp(stderr);
    rv=AUDITED_EBADKEY;
    goto free_bio;
  }

  did_init=true;

 free_bio:
  /* this does *not* free the underlying char* in this case, because
     BIO_new_mem_buf creates a read-only BIO */
  BIO_vfree(mem);
 out:
  return AUDITED_ENONE;
}

/* returned pointer is mallocd */
audited_err_t audited_get_audit_server_pub_pem(char **audit_pub_key_pem)
{
  BIO *bio;
  audited_err_t rv=0;
  int cryptorv;
  size_t len;

  *audit_pub_key_pem=NULL;

  bio = BIO_new(BIO_s_mem());
  if (!bio) {
    rv=AUDITED_ECRYPTO;
    goto out;
  }
  
  /*  1 for success or 0 for failure */
  cryptorv = PEM_write_bio_RSAPublicKey(bio, audit_pub_key);
  if(!cryptorv) {
    rv=AUDITED_ECRYPTO;
    goto free_bio;
  }

  /* copy to a plain old mallocd buffer, so that caller can free it */
  clone_mem_bio(bio, (void**)audit_pub_key_pem, &len);
  if(!audit_pub_key_pem) {
    rv=AUDITED_ECRYPTO;
    goto free_bio;
  }
  (*audit_pub_key_pem)[len] = '\0';

 free_bio:
  BIO_vfree(bio);
 out:
  return rv;
}

void audited_release_pending_cmd_id(int i)
{
  audited_pending_cmd_t *cmd;
  /* FIXME: handle multiple pending cmds */
  assert(i==0);
  assert(num_pending == 1);

  cmd = &pending_cmds[i];
  free(cmd->audit_string);
  if(cmd->fns && cmd->req) {
    protobuf_c_message_free_unpacked(cmd->req, NULL);
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

audited_err_t audited_start_cmd(const Audited__StartReq *startreq,
                                Audited__StartRes *startres)
{
  audited_err_t rv=0;
  ProtobufCMessage *req=NULL;
  audited_cmd_t *cmd_desc=NULL;
  char *audit_string=NULL;
  uint32_t pending_cmd_id;
  bool saved_pending_cmd=false;

  if(!did_init) {
    rv = AUDITED_EBADSTATE;
    goto out;
  }

  if (startreq->cmd >= audited_cmds_num) {
    rv = AUDITED_EBADAUDITEDCMD;
    goto out;
  }
  cmd_desc = &audited_cmds[startreq->cmd];
  assert(cmd_desc);

  req = protobuf_c_message_unpack(cmd_desc->req_descriptor,
                                  NULL,
                                  startreq->cmd_input.len,
                                  startreq->cmd_input.data);
  if (!req) {
    rv = AUDITED_EDECODE;
    goto out;
  }
  assert(cmd_desc->audit_string);
  startres->svc_err = cmd_desc->audit_string(req,
                                             &audit_string);
  if (startres->svc_err) {
    goto out;
  }

  pending_cmd_id = audited_save_pending_cmd(cmd_desc, req, audit_string);
  if (pending_cmd_id < 0) {
    rv = AUDITED_ESAVE;
    goto out;
  }
  saved_pending_cmd=true;

  startres->res = malloc(sizeof(Audited__StartRes__Res));
  if(!startres->res) {
    rv = AUDITED_ENOMEM;
    goto out;
  }
  *(startres->res) = (Audited__StartRes__Res)
    {
      .base = PROTOBUF_C_MESSAGE_INIT (&audited__start_res__res__descriptor),
      .pending_cmd_id = pending_cmd_id,
      .audit_nonce.data = pending_cmds[pending_cmd_id].audit_nonce,
      .audit_nonce.len = pending_cmds[pending_cmd_id].audit_nonce_len,
      .audit_string = audit_string,
    };

 out:
  if (rv || startres->svc_err) {
    if (saved_pending_cmd) {
      audited_release_pending_cmd_id(pending_cmd_id);
    } else {
      free(audit_string);
      if(req) {
        protobuf_c_message_free_unpacked(req, NULL);
      }
    }
    free(startres->res);
    startres->res=NULL;
  }
  return rv;
}

audited_err_t audited_execute_cmd(const Audited__ExecuteReq *exec_req,
                                  Audited__ExecuteRes *exec_res)
{
  audited_err_t rv;
  audited_pending_cmd_t *cmd;
  ProtobufCMessage *res=NULL;

  if(!did_init) {
    rv = AUDITED_EBADSTATE;
    goto out;
  }

  if (!(cmd = audited_pending_cmd_of_id(exec_req->pending_cmd_id))) {
    rv = AUDITED_EBADCMDHANDLE;
    goto out;
  }

  rv = audited_check_cmd_auth(cmd,
                              exec_req->audit_token.data,
                              exec_req->audit_token.len);
  if (rv) {
    goto out_release_pending_cmd;
  }

  assert(cmd->fns);
  assert(cmd->fns->execute);
  assert(cmd->fns->res_descriptor);

  res = malloc(cmd->fns->res_descriptor->sizeof_message);
  if(!res) {
    rv = AUDITED_ENOMEM;
    goto out_release_pending_cmd;
  }
  protobuf_c_message_init(cmd->fns->res_descriptor, res);

  exec_res->svc_err = cmd->fns->execute(cmd->req, res);
  if(exec_res->svc_err) {
    goto out_free_res;
  }

  exec_res->cmd_output.len = protobuf_c_message_get_packed_size(res);
  exec_res->cmd_output.data = malloc(exec_res->cmd_output.len);
  if(!exec_res->cmd_output.data) {
    rv = AUDITED_ENOMEM;
    goto out_release_res;
  }
  protobuf_c_message_pack(res, exec_res->cmd_output.data);
  exec_res->has_cmd_output=true;

 out_release_res:
  if (cmd->fns->release_res) {
    cmd->fns->release_res(res);
  }
 out_free_res:
  free(res);
  res=NULL;
 out_release_pending_cmd:
  audited_release_pending_cmd_id(exec_req->pending_cmd_id);
 out:
  return rv;
}

void audited_execute_cmd_release_res(Audited__ExecuteRes *exec_res)
{
  free(exec_res->cmd_output.data);
  exec_res->cmd_output.data=NULL;
}

