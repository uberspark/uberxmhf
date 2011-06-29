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

#ifndef KV_H
#define KV_H

#include <stddef.h>

struct kv_ctx_s;
typedef struct kv_ctx_s kv_ctx_t;

enum {
  KV_ENONE=0,
  KV_ENOTFOUND,
  KV_EEXISTS,
  KV_EFULL,
  KV_ENOMEM,
};

kv_ctx_t* kv_ctx_new(void);
void kv_ctx_del(kv_ctx_t*);

int kv_add(kv_ctx_t* ctx, const void *key, size_t key_len, const void *val, size_t val_len);
int kv_get(kv_ctx_t* ctx, const void *key, size_t key_len, const void **val, size_t *val_len);
int kv_del(kv_ctx_t* ctx, const void *key, size_t key_len);

int kv_import(kv_ctx_t* ctx, void *inbuf, size_t inbuf_sz);
int kv_export(kv_ctx_t* ctx, void **outbuf, size_t *outbuf_sz);

#endif
