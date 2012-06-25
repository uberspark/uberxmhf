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
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
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
#include <openssl/aes.h>

#include <string.h>

#include "dbg.h"
#include "audited-kv-pal-int.h"
#include "audited.h"
#include "audited-kv-pal-storage.h"
#include "kv.h"

/* static */ unsigned int align_up(unsigned int val, unsigned int align)
{
  return ((val-1) & ~(align-1)) + align;
}

static akv_err_t sha256_hmac_MacdEncdEntry(const AkvpStorage__MacdEncdEntry *entry,
                                           uint8_t *hmac,
                                           size_t hmac_len)
{ /* hmac */
  HMAC_CTX ctx;
  int cryptorv;
  akv_err_t rv=0;

  assert(hmac_len==SHA256_DIGEST_LENGTH);

  HMAC_CTX_init(&ctx);

  cryptorv = HMAC_Init_ex(&ctx,
                          akv_ctx.hmac_key,
                          akv_ctx.hmac_key_len,
                          EVP_sha256(), NULL);
  CHECK(cryptorv, AKV_ECRYPTO, "HMAC_Init_ex");

  cryptorv = HMAC_Update(&ctx, (uint8_t*)entry->key, strlen(entry->key));
  CHECK(cryptorv, AKV_ECRYPTO, "HMAC_Update");
  cryptorv = HMAC_Update(&ctx, entry->ivec.data, entry->ivec.len);
  CHECK(cryptorv, AKV_ECRYPTO, "HMAC_Update");
  cryptorv = HMAC_Update(&ctx, entry->encd_val.data, entry->encd_val.len);
  CHECK(cryptorv, AKV_ECRYPTO, "HMAC_Update");
    
  cryptorv = HMAC_Final(&ctx, hmac, &hmac_len);
  CHECK(cryptorv, AKV_ECRYPTO, "HMAC_Final");
  assert(hmac_len==SHA256_DIGEST_LENGTH);

 out:
  return rv;
}


static akv_err_t export_entry(AkvpStorage__MacdEncdEntry *out,
                              const char *key, size_t key_len,
                              const uint8_t *val,
                              size_t val_len)
{
  akv_err_t rv=0;
  unsigned int svcerr;

  *out = (AkvpStorage__MacdEncdEntry) {
    .base = PROTOBUF_C_MESSAGE_INIT (&akvp_storage__macd_encd_entry__descriptor),
  };

  { /* key */
    out->key=malloc(key_len+1);
    CHECK_MEM(out->key, AKV_ENOMEM);
    memcpy(out->key, key, key_len);
    ((char*)out->key)[key_len]='\0';
  }

  { /* ivec, encd_val */
    uint8_t ecount_buf[AES_BLOCK_SIZE];
    uint8_t ivec[AES_BLOCK_SIZE];
    unsigned int num=0;
    out->ivec.len=AES_BLOCK_SIZE;
    out->ivec.data=malloc(out->ivec.len);
    CHECK_MEM(out->ivec.data, AKV_ENOMEM);
    svcerr = svc_utpm_rand_block(out->ivec.data, out->ivec.len);
    CHECK_RV(svcerr, AKV_ESVC|svcerr<<8, "svc_utpm_rand_block");

    /* ivec gets updates on encrypt, so we need to make a copy */
    memcpy(ivec, out->ivec.data, AES_BLOCK_SIZE);

    out->encd_val.len = val_len;/* ctr-mode doesn't need padding. XXX
                                   consider padding so as not to leak
                                   length of plain-text */
    out->encd_val.data = malloc(out->encd_val.len); 
    CHECK_MEM(out->encd_val.data, AKV_ENOMEM);
    memset(ecount_buf, 0, sizeof(ecount_buf));
    AES_ctr128_encrypt(val, out->encd_val.data,
                       val_len, &akv_ctx.aes_ctr_key,
                       ivec,
                       ecount_buf,
                       &num);
    
  }

  { /* hmac */
    out->hmac.len=SHA256_DIGEST_LENGTH;
    out->hmac.data=malloc(out->hmac.len);
    CHECK_MEM(out->hmac.data, AKV_ENOMEM);
    rv = sha256_hmac_MacdEncdEntry(out,
                                   out->hmac.data,
                                   out->hmac.len);
    CHECK_RV(rv, rv, "sha256_hmac_MacdEncdEntry");
  }

 out:
  return rv;
}

static akv_err_t import_entry(const AkvpStorage__MacdEncdEntry *entry)
{
  akv_err_t rv=0;
  uint8_t *val=NULL;
  size_t val_len;

  { /* verify hmac */
    uint8_t hmac[SHA256_DIGEST_LENGTH];

    rv = sha256_hmac_MacdEncdEntry(entry, hmac, sizeof(hmac));
    CHECK_RV(rv, rv, "sha256_hmac_MacdEncdEntry");

    CHECK(!memcmp(hmac, entry->hmac.data, sizeof(hmac)),
          AKV_EBADMAC,
          "Bad hmac for entry %s", entry->key);
  }

  { /* decrypt */
    uint8_t ecount_buf[AES_BLOCK_SIZE];
    uint8_t ivec[AES_BLOCK_SIZE];
    unsigned int num=0;

    /* ivec gets updates on encrypt, so we need to make a copy */
    CHECK(entry->ivec.len == sizeof(ivec),
          AKV_EPARAM,
          "Bad ivec length for entry %s", entry->key);
    memcpy(ivec, entry->ivec.data, sizeof(ivec));

    val_len = entry->encd_val.len; /* plaintext is same size */
    val=malloc(val_len); 
    CHECK_MEM(val, AKV_ENOMEM);
    
    memset(ecount_buf, 0, sizeof(ecount_buf));
    AES_ctr128_encrypt(entry->encd_val.data, val,
                       val_len,
                       &akv_ctx.aes_ctr_key,
                       ivec,
                       ecount_buf,
                       &num);
  }

  { /* insert */
    kv_err_t kv_err;
    kv_err = kv_add(akv_ctx.kv_ctx,
                    entry->key, strlen(entry->key),
                    val, val_len);
    CHECK_RV(kv_err, MAP1(kv_err,
                          KV_EEXISTS, AKV_EEXISTS,
                          AKV_EKV | (kv_err << 8)),
             "kv_add %s", entry->key);
  }

 out:
  free(val);
  val=NULL;
  return rv;
}

static akv_err_t compute_header_mac(void *hmac_key,
                                    size_t hmac_key_len,
                                    const AkvpStorage__Header *h,
                                    uint8_t *md,
                                    size_t *md_len)
{
  HMAC_CTX ctx;
  int cryptorv;
  akv_err_t rv=0;

  HMAC_CTX_init(&ctx);

  cryptorv = HMAC_Init_ex(&ctx,
                          hmac_key, hmac_key_len,
                          EVP_sha256(), NULL);
  CHECK(cryptorv, AKV_ECRYPTO, "HMAC_Init_ex");

  cryptorv = HMAC_Update(&ctx, (uint8_t*)h->audit_pub_key_pem, strlen(h->audit_pub_key_pem));
  CHECK(cryptorv, AKV_ECRYPTO, "HMAC_Update");

  cryptorv = HMAC_Final(&ctx, md, md_len);
  CHECK(cryptorv, AKV_ECRYPTO, "HMAC_Final");
  
 out:
  HMAC_CTX_cleanup(&ctx);
  return rv;
}

static akv_err_t export_header(AkvpStorage__Header *h)
{
  akv_err_t rv=0;
  audited_err_t audited_err;
  char *audit_pub_key_pem;

  audited_err = audited_get_audit_server_pub_pem(&audit_pub_key_pem);
  CHECK_RV(audited_err, AKV_EAUDITED | (audited_err << 8),
           "audited_get_audit_server_pub_pem");

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
  uint32_t sizeof_pcrs=0;
  uint32_t sizeof_pcrs_be;
  int cryptorv;
  akv_err_t rv=0;

  SHA1_Init(&sha_ctx);

  cryptorv=SHA1_Update(&sha_ctx, pcr_selection, sizeof(*pcr_selection));
  CHECK(cryptorv, AKV_ECRYPTO, "SHA1_Update");

  for(i=0; i<TPM_PCR_NUM; i++) {
    if(utpm_pcr_is_selected(pcr_selection, i)) {
      sizeof_pcrs += TPM_HASH_SIZE;
    }
  }
  assert((sizeof_pcrs & 0xff) == sizeof_pcrs);
  sizeof_pcrs_be = sizeof_pcrs << 24; /* XXX quick and dirty
                                         conversion to big endian */
  cryptorv=SHA1_Update(&sha_ctx, &sizeof_pcrs_be, sizeof(sizeof_pcrs_be));
  CHECK(cryptorv, AKV_ECRYPTO, "SHA1_Update");
  
  for(i=0; i<TPM_PCR_NUM; i++) {
    if(utpm_pcr_is_selected(pcr_selection, i)) {
      svcrv = svc_utpm_pcr_read(i, &pcr[0]);
      CHECK_RV(svcrv, AKV_ESVC | (svcrv << 8), "svc_utpm_pcr_read");

      cryptorv = SHA1_Update(&sha_ctx, &pcr[0], TPM_HASH_SIZE);
      CHECK(cryptorv, AKV_ECRYPTO, "SHA1_Update");
    }
  }

  cryptorv = SHA1_Final(composite_hash->value, &sha_ctx);
  CHECK(cryptorv, AKV_ECRYPTO, "SHA1_Final");

 out:
  return rv;
}

akv_err_t akvp_export(const void *req, AkvpStorage__Everything *res)
{
  akv_err_t rv=0;
  AkvpStorage__Header *header;
  size_t sealed_master_secret_len=akv_ctx.master_secret_len+100;
  void *sealed_master_secret;
  uint8_t *header_mac=NULL;
  size_t header_mac_len=SHA256_DIGEST_LENGTH;
  size_t num_entries;
  AkvpStorage__MacdEncdEntry **entries;

  { /* seal master secret */
    TPM_PCR_INFO pcr_info;
    int svcrv;

    memset(&pcr_info, 0, sizeof(pcr_info));

    /* select pcr0 */
    utpm_pcr_select_i(&pcr_info.pcrSelection, 0); /* seal to code identity */

    rv = composite_hash_of_current_pcrs(&pcr_info.digestAtRelease,
                                        &pcr_info.pcrSelection);
    CHECK_RV(rv, rv, "composite_hash_of_current_pcrs");
    
    /* real uTPM ignores digestAtCreation, but null-backend
       for debugging will use this.
    */
    pcr_info.digestAtCreation = pcr_info.digestAtRelease;

    sealed_master_secret=malloc(sealed_master_secret_len);
    CHECK_MEM(sealed_master_secret, AKV_ENOMEM);

    svcrv = svc_utpm_seal(&pcr_info,
                          akv_ctx.master_secret,
                          akv_ctx.master_secret_len,
                          sealed_master_secret,
                          &sealed_master_secret_len);
    CHECK_RV(svcrv, AKV_ESVC | (svcrv << 8), "svc_utpm_seal");
  }

  { /* export and hmac header */
    header=malloc(sizeof(*header));
    CHECK_MEM(header, AKV_ENOMEM);

    rv = export_header(header);
    CHECK_RV(rv, rv, "export_header");

    header_mac = malloc(header_mac_len);
    CHECK_MEM(header_mac, AKV_ENOMEM);

    rv = compute_header_mac(akv_ctx.hmac_key, akv_ctx.hmac_key_len,
                            header,
                            header_mac, &header_mac_len);
    CHECK_RV(rv, rv, "compute_header_mac");
  }

  { /* export entries */
    kv_it_t it;
    const void *key, *val;
    size_t key_len, val_len;
    int i;
      
    num_entries = kv_count(akv_ctx.kv_ctx);
    entries = malloc(sizeof(*entries)*num_entries);
    CHECK_MEM(entries, AKV_ENOMEM);

    kv_iterate(akv_ctx.kv_ctx, &it);
    for(i=0; i<num_entries; i++) {
      kv_it_next(&it, &key, &key_len, &val, &val_len);
      assert(key && val);

      entries[i] = malloc(sizeof(*entries[i]));
      CHECK_MEM(entries[i], AKV_ENOMEM);

      rv = export_entry(entries[i], key, key_len, val, val_len);
      CHECK_RV(rv, rv, "export_entry");
    }
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
    .n_macd_encd_entries = num_entries,
    .macd_encd_entries = entries,
  };

 out:
  return rv;
}
void akvp_export_release_res(AkvpStorage__Everything *res)
{
  int i;
  akvp_storage__header__free_unpacked(res->header, NULL);
  free(res->sealed_master_secret.data);
  free(res->mac_of_header.data);

  for(i=0; i<res->n_macd_encd_entries; i++) {
    free(res->macd_encd_entries[i]->key);
    free(res->macd_encd_entries[i]->hmac.data);
    free(res->macd_encd_entries[i]->ivec.data);
    free(res->macd_encd_entries[i]->encd_val.data);
    free(res->macd_encd_entries[i]);
    res->macd_encd_entries[i]=NULL;
  }
}

akv_err_t akvp_import(const AkvpStorage__Everything *req, void *res)
{
  unsigned int svcrv;
  akv_err_t rv=0;
  TPM_DIGEST digest_at_creation;
  void *master_secret;
  size_t master_secret_len;
  uint8_t header_mac[SHA256_DIGEST_LENGTH];
  size_t header_mac_len=SHA256_DIGEST_LENGTH;

  master_secret = malloc(req->sealed_master_secret.len);
  CHECK_MEM(master_secret, AKV_ENOMEM);

  svcrv = svc_utpm_unseal(req->sealed_master_secret.data,
                          req->sealed_master_secret.len,
                          master_secret,
                          &master_secret_len,
                          &digest_at_creation);
  CHECK_RV(svcrv, AKV_ESVC | (svcrv << 8), "svc_utpm_unseal");

  /* check digest_at_creation
   * for now we just compare to our own current PCRs. eventually we'll
   * want to add more flexibility.
  */
  {
    TPM_DIGEST digest_now;
    TPM_PCR_SELECTION pcr_selection;

    /* select pcr0 */
    memset(&pcr_selection, 0, sizeof(pcr_selection));
    utpm_pcr_select_i(&pcr_selection, 0);

    rv = composite_hash_of_current_pcrs(&digest_now,
                                        &pcr_selection);
    CHECK_RV(rv, rv, "composite_hash_of_current_pcrs");

    if(memcmp(&digest_now, &digest_at_creation, sizeof(TPM_DIGEST))) {
      log_err("digest_at_creation doesn't match current PCRs");
      rv = AKV_EBADDIGESTATCREATION;
      goto out;
    }
  }

  rv = akvp_init_priv(req->header->audit_pub_key_pem,
                      master_secret,
                      master_secret_len);
  CHECK_RV(rv, rv, "akvp_init_priv");

  /* FIXME: should do this before full initialization, above */
  rv = compute_header_mac(akv_ctx.hmac_key, akv_ctx.hmac_key_len,
                          req->header,
                          header_mac, &header_mac_len);
  CHECK_RV(rv, rv, "compute_header_mac");

  if(memcmp(header_mac, req->mac_of_header.data, header_mac_len)) {
    rv = AKV_EBADMAC;
    goto out;
  }

  { /* import entries */
    int i;
    for(i=0; i<req->n_macd_encd_entries; i++) {
      rv = import_entry(req->macd_encd_entries[i]);
      CHECK_RV(rv, rv, "import_entry");
    }
  }

 out:
  /* in case of any sort of failure, invalidate akvp global state */
  if(rv) {
    akvp_uninit();
  }
  return rv;
}
