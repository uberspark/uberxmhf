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

#include "audited-kv-pal.h"
#include "proto-gend/audited.pb-c.h"
#include "proto-gend/akvp.pb-c.h"
#include "proto-gend/storage.pb-c.h"
const tze_pb_proto_t akvp_protos[] = {
  [AKVP_INIT] = {
    .req_descriptor = &akvp__init_req__descriptor,
    .res_descriptor = &akvp__init_res__descriptor,
  },
  [AKVP_START_AUDITED_CMD] = {
    .req_descriptor = &audited__start_req__descriptor,
    .res_descriptor = &audited__start_res__descriptor,
  },
  [AKVP_EXECUTE_AUDITED_CMD] = {
    .req_descriptor = &audited__execute_req__descriptor,
    .res_descriptor = &audited__execute_res__descriptor,
  },
  [AKVP_EXPORT] = {
    .req_descriptor = NULL,
    .res_descriptor = &akvp_storage__everything__descriptor,
  },
};

