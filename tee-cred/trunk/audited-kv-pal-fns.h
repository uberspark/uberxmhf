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

#ifndef AUDITED_KV_PAL_FNS_H
#define AUDITED_KV_PAL_FNS_H

#include <tee-sdk/tz.h>
#include "audited-kv-errs.h"

akv_err_t akvp_init(const char*);
void akvp_release(void);

int akvp_db_add_begin_decode_req(void **req,
                                 void *inbuf,
                                 size_t inbuf_len);
akv_err_t akvp_db_add_begin(void *req,
                            char **audit_string);
int akvp_db_add_execute(void* vreq, void **vres);
void akvp_db_add_release_req(void* req);
int akvp_db_add_audit_string(void *vreq,
                             char **audit_string);
size_t akvp_db_add_encode_res_len(void* vres);
void akvp_db_add_release_res(void* vres);
int akvp_db_add_encode_res(void *vres, void* buf);

int akvp_db_get_decode_req(void **req,
                           void *inbuf,
                           size_t inbuf_len);
int akvp_db_get_execute(void* vreq, void **vres);
void akvp_db_get_release_req(void* req);
int akvp_db_get_audit_string(void *vreq,
                             char **audit_string);
size_t akvp_db_get_encode_res_len(void* vres);
void akvp_db_get_release_res(void* vres);
int akvp_db_get_encode_res(void *vres, void* buf);

#endif
