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

#ifndef AUDIT_H
#define AUDIT_H

#include <stdint.h>

#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>

#define AUDIT_TOKEN_MAX 1000

enum {
  AUDIT_ENONE=0,
  AUDIT_ELOOKUP=1,
  AUDIT_ESOCK=2,
  AUDIT_ECONNECT=3,
  AUDIT_ESEND=4,
  AUDIT_ERECV=5,
  AUDIT_ESHORT_BUFFER=6,
};

typedef struct {
  const char* hostname;
  const char* svc;
} audit_ctx_t;

int audit_get_token(audit_ctx_t*    audit_ctx,
                    const uint8_t*  audit_nonce,
                    size_t          audit_nonce_len,
                    const char*     audit_string,
                    size_t          audit_string_len,
                    void*           audit_token,
                    size_t*         audit_token_len);

int audit_ctx_init(audit_ctx_t *ctx, const char* hostname, const char* svc);
void audit_ctx_release(audit_ctx_t *ctx);

#endif
