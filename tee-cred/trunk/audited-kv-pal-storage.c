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
#include <openssl/hmac.h>

#include <string.h>

#include "audited-kv-pal-int.h"
#include "audited.h"
#include "audited-kv-pal-storage.h"

static akv_err_t compute_header_mac(const AkvpStorage__Header *h,
                                    uint8_t *md,
                                    size_t *md_len)
{
  HMAC_CTX ctx;
  int cryptorv;
  akv_err_t rv=0;

  HMAC_CTX_init(&ctx);
  cryptorv = HMAC_Init_ex(&ctx,
                          akv_ctx.hmac_key, akv_ctx.hmac_key_len,
                          EVP_sha256(), NULL);
  if(!cryptorv) {
    rv = AKV_ECRYPTO;
    goto out;
  }

  cryptorv = HMAC_Update(&ctx, (uint8_t*)h->audit_pub_key_pem, strlen(h->audit_pub_key_pem));
  if(!cryptorv) {
    rv = AKV_ECRYPTO;
    goto cleanup_ctx;
  }

  cryptorv = HMAC_Final(&ctx, md, md_len);
  if(!cryptorv) {
    rv = AKV_ECRYPTO;
    goto cleanup_ctx;
  }

 cleanup_ctx:
  HMAC_CTX_cleanup(&ctx);
 out:
  return rv;
}
                                    

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

static akv_err_t composite_hash_of_current_pcrs(TPM_COMPOSITE_HASH *composite_hash,
                                                TPM_PCR_SELECTION *pcr_selection) /* FIXME: should be
                                                                                     const. need fo fix
                                                                                     utpm_pcr_is_selected
                                                                                     in tv_utpm.h */
{
  SHA_CTX sha_ctx;
  int i;
  uint8_t pcr[TPM_HASH_SIZE];
  int svcrv;
  uint32_t sizeof_pcrs;
  uint32_t sizeof_pcrs_be;

  SHA1_Init(&sha_ctx);
  SHA1_Update(&sha_ctx, pcr_selection, sizeof(*pcr_selection));

  for(i=0; i<TPM_PCR_NUM; i++) {
    if(utpm_pcr_is_selected(pcr_selection, i)) {
      sizeof_pcrs += TPM_HASH_SIZE;
    }
  }
  assert((sizeof_pcrs & 0xff) == sizeof_pcrs);
  sizeof_pcrs_be = sizeof_pcrs << 24; /* XXX quick and dirty
                                         conversion to big endian */
  SHA1_Update(&sha_ctx, &sizeof_pcrs_be, sizeof(sizeof_pcrs_be));
  
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
  uint8_t *header_mac=NULL;
  size_t header_mac_len=SHA256_DIGEST_LENGTH;

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
    if(svcrv) {
      rv = AKV_ESVC | (svcrv << 8);
      goto out;
    }
  }

  header=malloc(sizeof(*header));
  if(!header) {
    rv=AKV_ENOMEM;
    goto out;
  }

  rv = export_header(header);
  if(rv) {
    goto out;
  }

  header_mac=malloc(header_mac_len);
  if(!header_mac) {
    rv = AKV_ENOMEM;
    goto out;
  }
  rv = compute_header_mac(header, header_mac, &header_mac_len);
  if(rv) {
    goto out;
  }

  *res = (AkvpStorage__Everything) {
    .base =  PROTOBUF_C_MESSAGE_INIT (&akvp_storage__everything__descriptor),
    .sealed_master_secret = {
      .data=sealed_master_secret,
      .len=sealed_master_secret_len,
    },
    .header = header,
    .mac_of_header = {
      .data=header_mac,
      .len=header_mac_len,
    },
  };

 out:
  return rv;
}
void akvp_export_release_res(AkvpStorage__Everything *res)
{
  akvp_storage__header__free_unpacked(res->header, NULL);
  free(res->sealed_master_secret.data);
  free(res->mac_of_header.data);
}

akv_err_t akvp_import(const AkvpStorage__Everything *req, void *res)
{
  uint32_t svcrv;
  akv_err_t rv=0;
  TPM_DIGEST digest_at_creation;
  void *master_secret;
  size_t master_secret_len;
  uint8_t header_mac[SHA256_DIGEST_LENGTH];
  size_t header_mac_len=SHA256_DIGEST_LENGTH;

  master_secret = malloc(req->sealed_master_secret.len);
  if(!master_secret) {
    rv = AKV_ENOMEM;
    goto out;
  }
  svcrv = svc_utpm_unseal(req->sealed_master_secret.data,
                          req->sealed_master_secret.len,
                          master_secret,
                          &master_secret_len,
                          &digest_at_creation);
  if(svcrv) {
    rv= AKV_ESVC | (svcrv << 8);
    goto out;
  }

  rv = akvp_init_priv(req->header->audit_pub_key_pem,
                      master_secret,
                      master_secret_len);
  if(rv) {
    goto out;
  }

  /* FIXME: should do this before full initialization, above */
  rv = compute_header_mac(req->header, header_mac, &header_mac_len);
  if(rv) {
    goto out;
  }
  if(memcmp(header_mac, req->mac_of_header.data, header_mac_len)) {
    rv = AKV_EBADMAC;
    goto out;
  }

 out:
  return rv;
}

