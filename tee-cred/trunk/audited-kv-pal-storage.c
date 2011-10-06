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

#include <google/protobuf-c/protobuf-c.h>

#include "audited.h"
#include "audited-kv-pal-storage.h"

static akv_err_t export_header(AkvpStorage__Header *h)
{
  akv_err_t rv=0;
  audited_err_t audited_err;
  char *audit_pub_key_pem;

  audited_err = audited_get_audit_server_pub_pem(&audit_pub_key_pem);
  if(audited_err) {
    rv=AKV_EAUDITED | (audited_err << 8);
    goto out;
  }

  *h = (AkvpStorage__Header) {
    .base = PROTOBUF_C_MESSAGE_INIT (&akvp_storage__header__descriptor),
    .audit_pub_key_pem = audit_pub_key_pem,
  };

 out:
  return rv;
}

akv_err_t akvp_export(const void *req, AkvpStorage__Everything *res)
{
  akv_err_t rv=0;
  AkvpStorage__Header *header;

  header=malloc(sizeof(*header));
  if(!header) {
    rv=AKV_ENOMEM;
    goto out;
  }

  rv = export_header(header);
  *res = (AkvpStorage__Everything) {
    .base =  PROTOBUF_C_MESSAGE_INIT (&akvp_storage__everything__descriptor),
    .header = header,
  };

 out:
  return rv;
}

void akvp_export_release_res(AkvpStorage__Everything *res)
{
  akvp_storage__everything__free_unpacked(res, NULL);
}
