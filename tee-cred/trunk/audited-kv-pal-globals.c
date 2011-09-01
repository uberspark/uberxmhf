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

#include "audited-kv-pal-fns.h"
#include "audited-kv-pal.h"
#include "audited.h"

/* required by audited module */
audited_cmd_t audited_cmds[] = {
  [AKVP_DB_ADD] = {
    .decode_req=akvp_db_add_begin_decode_req,
    .audit_string=akvp_db_add_audit_string,
    .execute=akvp_db_add_execute,
    .encode_res_maxlen=akvp_db_add_encode_res_maxlen,
    .encode_res=akvp_db_add_encode_res,
    .release_req=akvp_db_add_release_req,
    .release_res=akvp_db_add_release_res,
  },
  [AKVP_DB_GET] = {
    .decode_req=NULL,
    .audit_string=NULL,
    .execute=NULL,
    .release_req=akvp_db_get_release,
  },
};
size_t audited_cmds_num = sizeof(audited_cmds)/sizeof(audited_cmd_t);

/* required by libnosys's sbrk */
char end[10*4096];
