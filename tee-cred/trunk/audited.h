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

#ifndef AUDITED_H
#define AUDITED_H

#include <tee-sdk/tzmarshal.h>

typedef int (audited_begin_fn)(char **, void **, struct tzi_encode_buffer_t *);
typedef int (audited_execute_fn)(void *, struct tzi_encode_buffer_t *);
typedef void (audited_release_fn)(void *);

typedef struct {
  char *audit_string;
  void *cont;
  audited_execute_fn *execute_fn;
  audited_release_fn *release_fn;
  uint64_t epoch_nonce;
  uint64_t epoch_offset;
  void *audit_nonce;
  size_t audit_nonce_len;
} audited_pending_cmd_t;

#define AUDITED_MAX_PENDING 100

void audited_release_pending_cmd_id(int i);
audited_pending_cmd_t* audited_pending_cmd_of_id(int i);
int audited_save_pending_cmd(char *audit_string, void *cont, audited_execute_fn execute_fn, audited_release_fn release_fn);

#endif
