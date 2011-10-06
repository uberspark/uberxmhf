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
#include <openssl/sha.h>

#include <string.h>

#include "audited-kv-pal-int.h"
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

akv_err_t composite_hash_of_current_pcrs(TPM_DIGEST *composite_hash,
                                         TPM_PCR_SELECTION *pcr_selection) /* FIXME: should be
                                                                              const. need fo fix
                                                                              utpm_pcr_is_selected
                                                                              in tv_utpm.h */
{
  SHA_CTX sha_ctx;
  int i;
  uint8_t pcr[TPM_HASH_SIZE];
  int svcrv;

  SHA1_Init(&sha_ctx);
  SHA1_Update(&sha_ctx, pcr_selection, sizeof(*pcr_selection));
  for(i=0; i<TPM_PCR_NUM; i++) {
    if(utpm_pcr_is_selected(pcr_selection, i)) {
      svcrv = svc_utpm_pcr_read(i, &pcr[0]);
      if(svcrv) {
        return AKV_ESVC | (svcrv << 8);
      }
      SHA1_Update(&sha_ctx, &pcr[0], TPM_HASH_SIZE);
    }
  }
  SHA1_Final(composite_hash->value, &sha_ctx);

  return 0;
}

akv_err_t akvp_export(const void *req, AkvpStorage__Everything *res)
{
  akv_err_t rv=0;
  AkvpStorage__Header *header;
  size_t sealed_master_secret_len=akv_ctx.master_secret_len+100;
  void *sealed_master_secret;

  {
    TPM_PCR_INFO pcr_info;
    int svcrv;

    memset(&pcr_info, 0, sizeof(pcr_info));

    /* select pcr0 */
    utpm_pcr_select_i(&pcr_info.pcrSelection, 0); /* seal to code identity */
    rv = composite_hash_of_current_pcrs(&pcr_info.digestAtRelease,
                                        &pcr_info.pcrSelection);
    if(rv) {
      goto out;
    }
    
    sealed_master_secret=malloc(sealed_master_secret_len);
    if(!sealed_master_secret) {
      rv = AKV_ENOMEM;
      goto out;
    }
    svcrv = svc_utpm_seal(&pcr_info,
                          akv_ctx.master_secret,
                          akv_ctx.master_secret_len,
                          sealed_master_secret,
                          &sealed_master_secret_len);
  }

  header=malloc(sizeof(*header));
  if(!header) {
    rv=AKV_ENOMEM;
    goto out;
  }

  rv = export_header(header);
  *res = (AkvpStorage__Everything) {
    .base =  PROTOBUF_C_MESSAGE_INIT (&akvp_storage__everything__descriptor),
    .sealed_master_secret = {
      .data=sealed_master_secret,
      .len=sealed_master_secret_len,
    },
    .header = header,
  };

 out:
  return rv;
}

void akvp_export_release_res(AkvpStorage__Everything *res)
{
  akvp_storage__everything__free_unpacked(res, NULL);
}
