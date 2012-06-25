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
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
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

#ifndef AUDITED_H
#define AUDITED_H

#include <tee-sdk/tzmarshal.h>
#include "tze-pb.h"
#include "proto-gend/audited.pb-c.h"

typedef enum {
  AUDITED_ENONE=0,
  AUDITED_EBADKEY=1,
  AUDITED_ETIMEOUT=2,
  AUDITED_EBADSIG=3,
  AUDITED_ENOMEM=4,
  AUDITED_ECRYPTO=5,
  AUDITED_EBADAUDITEDCMD=6,
  AUDITED_EBADSTATE=7,
  AUDITED_EBADCMDHANDLE=8,
  AUDITED_EDECODE=9,
  AUDITED_EAUDITSTRING=10,
  AUDITED_ESAVE=11,

  AUDITED_EPB_ERR=12,
  AUDITED_ESVC=13,
} audited_err_t;

typedef int (audited_audit_string_fn)(void *, char **);

typedef struct {
  const ProtobufCMessageDescriptor *req_descriptor;
  const ProtobufCMessageDescriptor *res_descriptor;
  tze_pb_execute_fn *execute;
  tze_pb_release_res_fn *release_res;
  audited_audit_string_fn *audit_string;
} audited_cmd_t;

typedef struct {
  char *audit_string;
  void *req;
  uint64_t epoch_nonce;
  uint64_t epoch_offset;
  void *audit_nonce;
  size_t audit_nonce_len;
  audited_cmd_t *fns;
} audited_pending_cmd_t;

#define AUDITED_MAX_PENDING 100
#define AUDITED_TIMEOUT_US (5ull*60ull*1000000ull)

/* to be supplied by module user */
extern audited_cmd_t audited_cmds[];
extern size_t audited_cmds_num;

audited_err_t audited_init(const char* audit_server_pub_pem);
audited_err_t audited_get_audit_server_pub_pem(char **audit_pub_key_pem);
void audited_release_pending_cmd_id(int i);
audited_pending_cmd_t* audited_pending_cmd_of_id(int i);
int audited_save_pending_cmd(audited_cmd_t *fns, void *req, char *audit_string);
audited_err_t audited_check_cmd_auth(audited_pending_cmd_t *cmd, const void* audit_token, size_t audit_token_len);

audited_err_t audited_start_cmd(const Audited__StartReq *startreq,
                                Audited__StartRes *startres);
audited_err_t audited_execute_cmd(const Audited__ExecuteReq *exec_req,
                                  Audited__ExecuteRes *exec_res);
void audited_execute_cmd_release_res(Audited__ExecuteRes *exec_res);

#endif
