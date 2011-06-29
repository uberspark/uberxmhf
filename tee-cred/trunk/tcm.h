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

#ifndef TCM_H
#define TCM_H

#include <stddef.h>

#include "audit.h"



/* enum tee_cred_pal_cmds { */
/*   TCP_AUDIT_GET_NONCE, /\* ()                -> random nonce *\/ */
/*   TCP_AUDIT_EXECUTE,   /\* random nonce, cmd -> f(cmd) *\/ */

/*   TCP_DB_ADD,          /\* key, val          -> ()  *\/ */
/*   TCP_DB_GET,          /\* key               -> val *\/ */
/*   TCP_DB_DEL,          /\* key               -> () *\/ */
/*   TCP_DB_EXPORT,       /\* ()                -> seal(db) *\/ */
/*   TCP_DB_IMPORT,       /\* seal(db)          -> () *\/ */
/*   TCP_DB_MIGRATE,      /\* dest-pubkey, cert-chain -> E(db) *\/ */
  
/*   TCP_PW_LOCK,         /\* ()                -> () *\/ */
/*   TCP_PW_UNLOCK,       /\* password          -> () *\/ */
/*   TCP_PW_CHANGE,       /\* oldpass, newpass  -> () *\/ */

/*   TCP_INIT,            /\* audit-pubkey, password -> () *\/ */
/* }; */

typedef struct tcm_handle {
  audit_handle_t* audit_handle;
  void* db;
  size_t db_len;
} tcm_handle_t;


int tcm_init(tcm_handle_t*,
             audit_handle_t*,
             const void *db,
             size_t db_len);

void tcm_release(tcm_handle_t*);

int tcm_db_add(struct tcm_handle*,
               const char* key,
               const char* val);

int tcm_db_get(struct tcm_handle*,
               const char* key,
               char* val,
               int val_len);

int tcm_db_del(struct tcm_handle*,
               const char* key);


#endif
