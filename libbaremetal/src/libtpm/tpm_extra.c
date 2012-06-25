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

/*
 * tpm.c: TPM-related support functions
 *
 * Copyright (c) 2006-2010, Intel Corporation
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above
 *     copyright notice, this list of conditions and the following
 *     disclaimer in the documentation and/or other materials provided
 *     with the distribution.
 *   * Neither the name of the Intel Corporation nor the names of its
 *     contributors may be used to endorse or promote products derived
 *     from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

/*
 * Modified for XMHF by jonmccune@cmu.edu, 2011.01.18
 *
 * "Extra" functions unnecessary in SL denoted as such.
 */

#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <print_hex.h>
#include <tpm.h>
#include <tomcrypt.h>
#include <sha1.h>

/* These go with _tpm_submit_cmd in tpm.c */
extern uint8_t     cmd_buf[TPM_CMD_SIZE_MAX];
extern uint8_t     rsp_buf[TPM_RSP_SIZE_MAX];


static int sha1_id = -1;

/* compatibility wrapper */
static void HMAC_SHA1( uint8_t* secret, size_t secret_len,
                       uint8_t* in, size_t in_len,
                       uint8_t* out)
{
  int rv;
  unsigned long out_len;

  if (sha1_id < 0) {
    sha1_id = register_hash( &sha1_desc);
  }

  out_len = hash_descriptor[sha1_id].hashsize;
  rv = hmac_memory( sha1_id,
                    secret, secret_len,
                    in, in_len,
                    out, &out_len);
  if (rv) {
    abort();
  }
}

uint32_t tpm_pcr_reset(uint32_t locality, uint32_t pcr)
{
    uint32_t ret, in_size, out_size = 0;
    uint16_t size_of_select;
    tpm_pcr_selection_t pcr_sel = {0,{0,}};

    if ( pcr >= TPM_NR_PCRS || pcr < TPM_PCR_RESETABLE_MIN )
        return TPM_BAD_PARAMETER;

    /* the pcr_sel.pcr_select[size_of_select - 1] should not be 0 */
    size_of_select = pcr / 8 + 1;
    reverse_copy(&pcr_sel.size_of_select, &size_of_select,
                 sizeof(size_of_select));
    pcr_sel.pcr_select[pcr / 8] = 1 << (pcr % 8);

    in_size = sizeof(pcr_sel);
    memcpy(WRAPPER_IN_BUF, (void *)&pcr_sel, in_size);

    ret = tpm_submit_cmd(locality, TPM_ORD_PCR_RESET, in_size, &out_size);

    printf("TPM: Pcr %d reset, return value = %08X\n", pcr, ret);

    return ret;
}

uint32_t tpm_nv_read_value(uint32_t locality, tpm_nv_index_t index,
                           uint32_t offset, uint8_t *data,
                           uint32_t *data_size)
{
    uint32_t ret, in_size = 0, out_size;

    if ( data == NULL || data_size == NULL )
        return TPM_BAD_PARAMETER;
    if ( *data_size == 0 )
        return TPM_BAD_PARAMETER;
    if ( *data_size > TPM_NV_READ_VALUE_DATA_SIZE_MAX )
        *data_size = TPM_NV_READ_VALUE_DATA_SIZE_MAX;

    /* copy the index, offset and *data_size into buf in reversed byte order */
    reverse_copy(WRAPPER_IN_BUF, &index, sizeof(index));
    in_size += sizeof(index);
    reverse_copy(WRAPPER_IN_BUF + in_size, &offset, sizeof(offset));
    in_size += sizeof(offset);
    reverse_copy(WRAPPER_IN_BUF + in_size, data_size, sizeof(*data_size));
    in_size += sizeof(*data_size);

    out_size = *data_size + sizeof(*data_size);
    ret = tpm_submit_cmd(locality, TPM_ORD_NV_READ_VALUE, in_size, &out_size);

#ifdef TPM_TRACE
    printf("TPM: read nv index %08x from offset %08x, return value = %08X\n",
           index, offset, ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: read nv index %08x offset %08x, return value = %08X\n",
               index, offset, ret);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, WRAPPER_OUT_BUF, out_size);
    }
#endif

    if ( out_size <= sizeof(*data_size) ) {
        *data_size = 0;
        return ret;
    }

    out_size -= sizeof(*data_size);
    reverse_copy(data_size, WRAPPER_OUT_BUF, sizeof(*data_size));
    *data_size = (*data_size > out_size) ? out_size : *data_size;
    if( *data_size > 0 )
        memcpy(data, WRAPPER_OUT_BUF + sizeof(*data_size), *data_size);

    return ret;
}

uint32_t tpm_nv_write_value(uint32_t locality, tpm_nv_index_t index,
                            uint32_t offset, const uint8_t *data,
                            uint32_t data_size)
{
    uint32_t ret, in_size = 0, out_size = 0;

    if ( data == NULL )
        return TPM_BAD_PARAMETER;
    if ( data_size == 0 || data_size > TPM_NV_WRITE_VALUE_DATA_SIZE_MAX )
        return TPM_BAD_PARAMETER;

    /* copy index, offset and *data_size into buf in reversed byte order */
    reverse_copy(WRAPPER_IN_BUF, &index, sizeof(index));
    in_size += sizeof(index);
    reverse_copy(WRAPPER_IN_BUF + in_size, &offset, sizeof(offset));
    in_size += sizeof(offset);
    reverse_copy(WRAPPER_IN_BUF + in_size, &data_size, sizeof(data_size));
    in_size += sizeof(data_size);
    memcpy(WRAPPER_IN_BUF + in_size, data, data_size);
    in_size += data_size;

    ret = tpm_submit_cmd(locality, TPM_ORD_NV_WRITE_VALUE,
                         in_size, &out_size);

#ifdef TPM_TRACE
    printf("TPM: write nv %08x, offset %08x, %08x bytes, return = %08X\n",
           index, offset, data_size, ret);
#endif
    if ( ret != TPM_SUCCESS )
        printf("TPM: write nv %08x, offset %08x, %08x bytes, return = %08X\n",
               index, offset, data_size, ret);

    return ret;
}


static inline uint32_t tpm_submit_cmd_auth1(uint32_t locality, uint32_t cmd,
                                      uint32_t arg_size, uint32_t *out_size)
{
   return  _tpm_submit_cmd(locality, TPM_TAG_RQU_AUTH1_COMMAND, cmd,
                           arg_size, out_size);
}

static inline uint32_t tpm_submit_cmd_auth2(uint32_t locality, uint32_t cmd,
                                      uint32_t arg_size, uint32_t *out_size)
{
   return  _tpm_submit_cmd(locality, TPM_TAG_RQU_AUTH2_COMMAND, cmd,
                           arg_size, out_size);
}

static uint32_t tpm_oiap(uint32_t locality, tpm_authhandle_t *hauth,
                         tpm_nonce_t *nonce_even)
{
    uint32_t ret, offset, out_size;

    if ( hauth == NULL || nonce_even == NULL )
        return TPM_BAD_PARAMETER;

    offset = 0;

    out_size = sizeof(*hauth) + sizeof(*nonce_even);

    ret = tpm_submit_cmd(locality, TPM_ORD_OIAP, offset, &out_size);

#ifdef TPM_TRACE
    printf("TPM: start OIAP, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: start OIAP, return value = %08X\n", ret);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, WRAPPER_OUT_BUF, out_size);
    }
#endif

    offset = 0;
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *hauth);
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, nonce_even);

    return ret;
}

static uint32_t tpm_osap(uint32_t locality, tpm_entity_type_t ent_type,
                         uint32_t ent_value, const tpm_nonce_t *odd_osap,
                         tpm_authhandle_t *hauth, tpm_nonce_t *nonce_even,
                         tpm_nonce_t *even_osap)
{
    uint32_t ret, offset, out_size;

    if ( odd_osap == NULL || hauth == NULL ||
         nonce_even == NULL || even_osap == NULL )
        return TPM_BAD_PARAMETER;

    offset = 0;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, ent_type);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, ent_value);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, odd_osap);

    out_size = sizeof(*hauth) + sizeof(*nonce_even) + sizeof(*even_osap);
    ret = tpm_submit_cmd(locality, TPM_ORD_OSAP, offset, &out_size);

#ifdef TPM_TRACE
    printf("TPM: start OSAP, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: start OSAP, return value = %08X\n", ret);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, WRAPPER_OUT_BUF, out_size);
    }
#endif

    offset = 0;
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *hauth);
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, nonce_even);
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, even_osap);

    return ret;
}

static uint32_t _tpm_seal(uint32_t locality, tpm_key_handle_t hkey,
                  const tpm_encauth_t *enc_auth, uint32_t pcr_info_size,
                  const tpm_pcr_info_long_t *pcr_info, uint32_t in_data_size,
                  const uint8_t *in_data,
                  tpm_authhandle_t hauth, const tpm_nonce_t *nonce_odd,
                  uint8_t *cont_session, const tpm_authdata_t *pub_auth,
                  uint32_t *sealed_data_size, uint8_t *sealed_data,
                  tpm_nonce_t *nonce_even, tpm_authdata_t *res_auth)
{
    uint32_t ret, offset, out_size;

    if ( enc_auth == NULL || pcr_info == NULL || in_data == NULL ||
         nonce_odd == NULL || cont_session == NULL || pub_auth == NULL ||
         sealed_data_size == NULL || sealed_data == NULL ||
         nonce_even == NULL || res_auth == NULL ) {
        printf("TPM: _tpm_seal() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, hkey);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, enc_auth);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, pcr_info_size);
    UNLOAD_PCR_INFO_LONG(WRAPPER_IN_BUF, offset, pcr_info);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, in_data_size);
    UNLOAD_BLOB(WRAPPER_IN_BUF, offset, in_data, in_data_size);

    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, hauth);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, nonce_odd);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, *cont_session);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, pub_auth);

    out_size = WRAPPER_OUT_MAX_SIZE;

    ret = tpm_submit_cmd_auth1(locality, TPM_ORD_SEAL, offset, &out_size);

#ifdef TPM_TRACE
    printf("TPM: seal data, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: seal data, return value = %08X\n", ret);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, WRAPPER_OUT_BUF, out_size);
    }
#endif

    if ( *sealed_data_size <
         ( out_size - sizeof(*nonce_even) - sizeof(*cont_session)
           - sizeof(*res_auth) ) ) {
        printf("TPM: sealed blob is too small\n");
        return TPM_NOSPACE;
    }

    offset = 0;
    LOAD_STORED_DATA12(WRAPPER_OUT_BUF, offset, sealed_data);
    *sealed_data_size = offset;
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, nonce_even);
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *cont_session);
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, res_auth);

    return ret;
}

static uint32_t _tpm_unseal(uint32_t locality, tpm_key_handle_t hkey,
                    const uint8_t *in_data,
                    tpm_authhandle_t hauth, const tpm_nonce_t *nonce_odd,
                    uint8_t *cont_session, const tpm_authdata_t *auth,
                    tpm_authhandle_t hauth_d, const tpm_nonce_t *nonce_odd_d,
                    uint8_t *cont_session_d, const tpm_authdata_t *auth_d,
                    uint32_t *secret_size, uint8_t *secret,
                    tpm_nonce_t *nonce_even, tpm_authdata_t *res_auth,
                    tpm_nonce_t *nonce_even_d, tpm_authdata_t *res_auth_d)
{
    uint32_t ret, offset, out_size;

    if ( in_data == NULL || nonce_odd == NULL || cont_session == NULL ||
         auth == NULL || nonce_odd_d == NULL || cont_session_d == NULL ||
         auth_d == NULL || secret_size == NULL || secret == NULL ||
         nonce_even == NULL || res_auth == NULL || nonce_even_d == NULL ||
         res_auth_d == NULL ) {
        printf("TPM: _tpm_unseal() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, hkey);
    UNLOAD_STORED_DATA12(WRAPPER_IN_BUF, offset, in_data);

    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, hauth);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, nonce_odd);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, *cont_session);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, auth);

    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, hauth_d);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, nonce_odd_d);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, *cont_session_d);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, auth_d);

    out_size = WRAPPER_OUT_MAX_SIZE;

    ret = tpm_submit_cmd_auth2(locality, TPM_ORD_UNSEAL, offset, &out_size);

#ifdef TPM_TRACE
    printf("TPM: unseal data, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: unseal data, return value = %08X\n", ret);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, WRAPPER_OUT_BUF, out_size);
    }
#endif

    if ( *secret_size <
         ( out_size - sizeof(*secret_size) - sizeof(*nonce_even)
           - sizeof(*cont_session) - sizeof(*res_auth) - sizeof(*nonce_even_d)
           - sizeof(*cont_session_d) - sizeof(*res_auth_d) ) ) {
        printf("TPM: unsealed data too small\n");
        return TPM_NOSPACE;
    }

    offset = 0;
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *secret_size);
    LOAD_BLOB(WRAPPER_OUT_BUF, offset, secret, *secret_size);

    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, nonce_even);
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *cont_session);
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, res_auth);

    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, nonce_even_d);
    LOAD_INTEGER(WRAPPER_OUT_BUF, offset, *cont_session_d);
    LOAD_BLOB_TYPE(WRAPPER_OUT_BUF, offset, res_auth_d);

    return ret;
}


static const tpm_authdata_t srk_authdata =
    {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
static const tpm_authdata_t blob_authdata =
    {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

static uint32_t _tpm_wrap_seal(uint32_t locality,
                              const tpm_pcr_info_long_t *pcr_info,
                              uint32_t in_data_size, const uint8_t *in_data,
                              uint32_t *sealed_data_size, uint8_t *sealed_data)
{
    uint32_t ret;
    tpm_nonce_t odd_osap, even_osap, nonce_even, nonce_odd;
    tpm_authhandle_t hauth;
    tpm_authdata_t shared_secret, pub_auth, res_auth;
    tpm_encauth_t enc_auth;
    uint8_t cont_session = false;
    tpm_key_handle_t hkey = TPM_KH_SRK;
    uint32_t pcr_info_size = sizeof(*pcr_info);
    uint32_t offset;
    uint32_t ordinal = TPM_ORD_SEAL;
    tpm_digest_t digest;

    /* skip generate nonce for odd_osap, just use the random value in stack */

    /* establish a osap session */
    ret = tpm_osap(locality, TPM_ET_SRK, TPM_KH_SRK, &odd_osap, &hauth,
                   &nonce_even, &even_osap);
    if ( ret != TPM_SUCCESS )
            return ret;

    /* calculate the shared secret
       shared-secret = HMAC(srk_auth, even_osap || odd_osap) */
    offset = 0;
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &even_osap);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &odd_osap);
    HMAC_SHA1((uint8_t *)&srk_authdata, sizeof(srk_authdata),
              WRAPPER_IN_BUF, offset,
              (uint8_t *)&shared_secret);

    /* generate ecrypted authdata for data
       enc_auth = XOR(authdata, sha1(shared_secret || last_even_nonce)) */
    offset = 0;
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &shared_secret);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_even);
    sha1_buffer(WRAPPER_IN_BUF, offset, (uint8_t *)&digest);
    memcpy(&enc_auth, &blob_authdata, sizeof(blob_authdata));
    XOR_BLOB_TYPE(&enc_auth, &digest);

    /* skip generate nonce for nonce_odd, just use the random value in stack */

    /* calculate authdata */
    /* in_param_digest = sha1(1S ~ 6S) */
    offset = 0;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, ordinal);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &enc_auth);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, pcr_info_size);
    UNLOAD_PCR_INFO_LONG(WRAPPER_IN_BUF, offset, pcr_info);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, in_data_size);
    UNLOAD_BLOB(WRAPPER_IN_BUF, offset, in_data, in_data_size);
    sha1_buffer(WRAPPER_IN_BUF, offset, (uint8_t *)&digest);

    /* authdata = hmac(key, in_param_digest || auth_params) */
    offset = 0;
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &digest);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_even);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_odd);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, cont_session);
    HMAC_SHA1((uint8_t *)&shared_secret, sizeof(shared_secret),
              WRAPPER_IN_BUF, offset,
              (uint8_t *)&pub_auth);

    /* call the simple seal function */
    ret = _tpm_seal(locality, hkey, (const tpm_encauth_t *)&enc_auth,
                    pcr_info_size, pcr_info, in_data_size, in_data,
                    hauth, &nonce_odd, &cont_session,
                    (const tpm_authdata_t *)&pub_auth,
                    sealed_data_size, sealed_data,
                    &nonce_even, &res_auth);

    /* skip check for res_auth */

    return ret;
}

static uint32_t _tpm_wrap_unseal(uint32_t locality, const uint8_t *in_data,
                                 uint32_t *secret_size, uint8_t *secret)
{
    uint32_t ret;
    tpm_nonce_t odd_osap, even_osap;
    tpm_nonce_t nonce_even, nonce_odd, nonce_even_d, nonce_odd_d;
    tpm_authhandle_t hauth, hauth_d;
    tpm_authdata_t shared_secret;
    tpm_authdata_t pub_auth, res_auth, pub_auth_d, res_auth_d;
    uint8_t cont_session = false, cont_session_d = false;
    tpm_key_handle_t hkey = TPM_KH_SRK;
    uint32_t offset;
    uint32_t ordinal = TPM_ORD_UNSEAL;
    tpm_digest_t digest;

    /* skip generate nonce for odd_osap, just use the random value in stack */

    /* establish a osap session */
    ret = tpm_osap(locality, TPM_ET_SRK, TPM_KH_SRK, &odd_osap, &hauth,
                   &nonce_even, &even_osap);
    if ( ret != TPM_SUCCESS )
            return ret;

    /* calculate the shared secret
       shared-secret = HMAC(auth, even_osap || odd_osap) */
    offset = 0;
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &even_osap);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &odd_osap);
    HMAC_SHA1((uint8_t *)&srk_authdata, sizeof(srk_authdata),
              WRAPPER_IN_BUF, offset,
              (uint8_t *)&shared_secret);

    /* establish a oiap session */
    ret = tpm_oiap(locality, &hauth_d, &nonce_even_d);
    if ( ret != TPM_SUCCESS )
            return ret;

    /* skip generate nonce_odd & nonce_odd_d, just use the random values */

    /* calculate authdata */
    /* in_param_digest = sha1(1S ~ 6S) */
    offset = 0;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, ordinal);
    UNLOAD_STORED_DATA12(WRAPPER_IN_BUF, offset, in_data);
    sha1_buffer(WRAPPER_IN_BUF, offset, (uint8_t *)&digest);

    /* authdata1 = hmac(key, in_param_digest || auth_params1) */
    offset = 0;
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &digest);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_even);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_odd);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, cont_session);
    HMAC_SHA1((uint8_t *)&shared_secret, sizeof(shared_secret),
              WRAPPER_IN_BUF, offset,
              (uint8_t *)&pub_auth);

    /* authdata2 = hmac(key, in_param_digest || auth_params2) */
    offset = 0;
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &digest);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_even_d);
    UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, &nonce_odd_d);
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, cont_session_d);
    HMAC_SHA1((uint8_t *)&blob_authdata, sizeof(blob_authdata),
              WRAPPER_IN_BUF, offset,
              (uint8_t *)&pub_auth_d);

    /* call the simple seal function */
    ret = _tpm_unseal(locality, hkey, in_data,
                      hauth, &nonce_odd, &cont_session,
                      (const tpm_authdata_t *)&pub_auth,
                      hauth_d, &nonce_odd_d, &cont_session_d,
                      (const tpm_authdata_t *)&pub_auth_d,
                      secret_size, secret,
                      &nonce_even, &res_auth, &nonce_even_d, &res_auth_d);

    /* skip check for res_auth */

    return ret;
}

static bool init_pcr_info(uint32_t locality,
                          tpm_locality_selection_t release_locs,
                          uint32_t nr_create, const uint8_t indcs_create[],
                          uint32_t nr_release, const uint8_t indcs_release[],
                          const tpm_pcr_value_t *values_release[],
                          tpm_pcr_info_long_t *pcr_info)
{
    uint32_t offset;
    uint32_t i, blob_size;
    static tpm_locality_selection_t localities[TPM_NR_LOCALITIES] = {
        TPM_LOC_ZERO, TPM_LOC_ONE, TPM_LOC_TWO, TPM_LOC_THREE, TPM_LOC_FOUR
    };


    if ( (release_locs & TPM_LOC_RSVD) != 0 )
        return TPM_BAD_PARAMETER;
    if ( pcr_info == NULL )
        return TPM_BAD_PARAMETER;
    if ( locality >= TPM_NR_LOCALITIES )
        return TPM_BAD_PARAMETER;
    if ( indcs_create == NULL )
        nr_create = 0;
    if ( indcs_release == NULL || values_release == NULL )
        nr_release = 0;
    for ( i = 0; i < nr_create; i++ )
        if ( indcs_create[i] >= TPM_NR_PCRS )
            return TPM_BAD_PARAMETER;
    for ( i = 0; i < nr_release; i++ ) {
        if ( indcs_release[i] >= TPM_NR_PCRS || values_release[i] == NULL )
            return TPM_BAD_PARAMETER;
    }

    memset(pcr_info, 0, sizeof(*pcr_info));
    pcr_info->tag = TPM_TAG_PCR_INFO_LONG;
    pcr_info->locality_at_creation = localities[locality];
    pcr_info->locality_at_release = release_locs;
    pcr_info->creation_pcr_selection.size_of_select = 3;
    for ( i = 0; i < nr_create; i++ )
        pcr_info->creation_pcr_selection.pcr_select[indcs_create[i]/8] |=
            1 << (indcs_create[i] % 8);
    pcr_info->release_pcr_selection.size_of_select = 3;
    for ( i = 0; i < nr_release; i++ )
        pcr_info->release_pcr_selection.pcr_select[indcs_release[i]/8] |=
            1 << (indcs_release[i] % 8);

    if ( nr_release > 0 ) {
        offset = 0;
        UNLOAD_PCR_SELECTION(WRAPPER_IN_BUF, offset,
                             &pcr_info->release_pcr_selection);
        blob_size = sizeof(tpm_pcr_value_t) * nr_release;
        UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, blob_size);
        for ( i = 0; i < nr_release; i++ )
            UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, values_release[i]);
        sha1_buffer(WRAPPER_IN_BUF, offset,
                    (uint8_t *)&pcr_info->digest_at_release);
    }

    return true;
}

uint32_t tpm_seal(uint32_t locality, tpm_locality_selection_t release_locs,
                  uint32_t pcr_nr_create, const uint8_t pcr_indcs_create[],
                  uint32_t pcr_nr_release, const uint8_t pcr_indcs_release[],
                  const tpm_pcr_value_t *pcr_values_release[],
                  uint32_t in_data_size, const uint8_t *in_data,
                  uint32_t *sealed_data_size, uint8_t *sealed_data)
{
    uint32_t ret;
    tpm_pcr_info_long_t pcr_info;

    if ( locality >= TPM_NR_LOCALITIES ||
         in_data_size == 0 || in_data == NULL ||
         sealed_data_size == NULL || sealed_data == NULL ||
         *sealed_data_size == 0 ) {
        printf("TPM: tpm_seal() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    if ( !init_pcr_info(locality, release_locs, pcr_nr_create,
                        pcr_indcs_create, pcr_nr_release, pcr_indcs_release,
                        pcr_values_release, &pcr_info) ) {
        printf("TPM: tpm_seal() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    ret = _tpm_wrap_seal(locality, &pcr_info, in_data_size, in_data,
                         sealed_data_size, sealed_data);

    return ret;
}

static bool check_sealed_data(uint32_t size, const uint8_t *data)
{
    if ( size < sizeof(tpm_stored_data12_header_t) )
        return false;
    if ( ((const tpm_stored_data12_header_t *)data)->tag != TPM_TAG_STORED_DATA12 )
        return false;

    if ( ((const tpm_stored_data12_header_t *)data)->seal_info_size == 0 ) {
        const tpm_stored_data12_short_t *data12_s;

        if ( size < sizeof(*data12_s) )
            return false;
        data12_s = (const tpm_stored_data12_short_t *)data;
        if ( size != sizeof(*data12_s) + data12_s->enc_data_size )
            return false;
    }
    else {
        const tpm_stored_data12_t *data12;

        if ( size < sizeof(*data12) )
            return false;
        data12 = (const tpm_stored_data12_t *)data;
        if ( size != sizeof(*data12) + data12->enc_data_size )
            return false;
    }

    return true;
}

uint32_t tpm_unseal(uint32_t locality,
                    uint32_t sealed_data_size, const uint8_t *sealed_data,
                    uint32_t *secret_size, uint8_t *secret)
{
    uint32_t ret;

    if ( sealed_data == NULL ||
         secret_size == NULL || secret == NULL ) {
        printf("TPM: tpm_unseal() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    if ( !check_sealed_data(sealed_data_size, sealed_data) ) {
        printf("TPM: tpm_unseal() blob invalid\n");
        return TPM_BAD_PARAMETER;
    }

    ret = _tpm_wrap_unseal(locality, sealed_data, secret_size, secret);

    return ret;
}

static void calc_pcr_composition(uint32_t nr, const uint8_t indcs[],
                                 const tpm_pcr_value_t *values[],
                                 tpm_composite_hash_t *composite)
{
    uint32_t i, offset, blob_size;
    tpm_pcr_selection_t sel;

    if ( nr == 0 || indcs == NULL || values == NULL || composite == NULL)
        return;

    sel.size_of_select = 3;
    sel.pcr_select[0] = sel.pcr_select[1] = sel.pcr_select[2] = 0;
    for ( i = 0; i < nr; i++ )
        sel.pcr_select[indcs[i]/8] |= 1 << (indcs[i] % 8);

    offset = 0;
    UNLOAD_PCR_SELECTION(WRAPPER_IN_BUF, offset, &sel);
    blob_size = sizeof(tpm_pcr_value_t) * nr;
    UNLOAD_INTEGER(WRAPPER_IN_BUF, offset, blob_size);
    for ( i = 0; i < nr; i++ )
        UNLOAD_BLOB_TYPE(WRAPPER_IN_BUF, offset, values[i]);
    sha1_buffer(WRAPPER_IN_BUF, offset, (uint8_t *)composite);
}

static tpm_composite_hash_t *get_cre_pcr_composite(uint8_t *data)
{
    if ( ((tpm_stored_data12_header_t *)data)->seal_info_size == 0 )
        return NULL;
    else
        return &((tpm_stored_data12_t *)data)->seal_info.digest_at_creation;
}

bool tpm_cmp_creation_pcrs(uint32_t pcr_nr_create,
                           const uint8_t pcr_indcs_create[],
                           const tpm_pcr_value_t *pcr_values_create[],
                           uint32_t sealed_data_size, uint8_t *sealed_data)
{
    uint32_t i;
    tpm_composite_hash_t composite = {{0,}}, *cre_composite;

    if ( pcr_indcs_create == NULL )
        pcr_nr_create = 0;
    for ( i = 0; i < pcr_nr_create; i++ ) {
        if ( pcr_indcs_create[i] >= TPM_NR_PCRS )
            return false;
    }
    if ( !check_sealed_data(sealed_data_size, sealed_data) ) {
        printf("TPM: Bad blob.\n");
        return false;
    }

    if ( pcr_nr_create > 0 )
        calc_pcr_composition(pcr_nr_create, pcr_indcs_create,
                             pcr_values_create, &composite);

    cre_composite = get_cre_pcr_composite(sealed_data);
    if ( cre_composite == NULL )
        return false;
    if ( memcmp((char*)&composite, (char*)cre_composite, sizeof(composite)) ) {
        printf("TPM: Not equal to creation composition:\n");
        print_hex(NULL, (uint8_t *)&composite, sizeof(composite));
        print_hex(NULL, (uint8_t *)cre_composite, sizeof(composite));
        return false;
    }

    return true;
}


uint32_t tpm_get_nvindex_size(uint32_t locality,
                              tpm_nv_index_t index, uint32_t *size)
{
    uint32_t ret, offset, resp_size;
    uint8_t sub_cap[sizeof(index)];
    uint8_t resp[sizeof(tpm_nv_data_public_t)];
    tpm_nv_index_t idx;

    if ( size == NULL ) {
        printf("TPM: tpm_get_nvindex_size() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(sub_cap, offset, index);

    resp_size = sizeof(resp);
    ret = tpm_get_capability(locality, TPM_CAP_NV_INDEX, sizeof(sub_cap),
                             sub_cap, &resp_size, resp);

#ifdef TPM_TRACE
    printf("TPM: get nvindex size, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: fail to get public data of 0x%08X in TPM NV\n", index);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, resp, resp_size);
    }
#endif

    /* check size */
    if ( resp_size == 0 ) {
        printf("TPM: Index 0x%08X does not exist\n", index);
        return TPM_BADINDEX;
    }

    /* check index */
    offset = sizeof(tpm_structure_tag_t);
    LOAD_INTEGER(resp, offset, idx);
#ifdef TPM_TRACE
    printf("TPM: get index value = %08X\n", idx);
#endif

    if ( idx != index ) {
        printf("TPM: Index 0x%08X is not the one expected 0x%08X\n",
               idx, index);
        return TPM_BADINDEX;
    }

    if ( resp_size != sizeof(resp) ) {
        printf("TPM: public data size of Index 0x%08X responsed incorrect\n",
               index);
        return TPM_FAIL;
    }

    offset = resp_size - sizeof(uint32_t);
    LOAD_INTEGER(resp, offset, *size);

    return ret;
}

extern uint32_t tpm_get_nv_data_public(uint32_t locality,
                                       tpm_nv_index_t index,
                                       tpm_nv_data_public_t *pub)
{
    uint32_t ret, offset, resp_size;
    uint8_t sub_cap[sizeof(index)];
    uint8_t resp[sizeof(tpm_nv_data_public_t)];
    tpm_nv_index_t idx;

    if ( pub == NULL ) {
        printf("TPM: tpm_get_nvindex_size() bad parameter\n");
        return TPM_BAD_PARAMETER;
    }

    offset = 0;
    UNLOAD_INTEGER(sub_cap, offset, index);

    resp_size = sizeof(resp);
    ret = tpm_get_capability(locality, TPM_CAP_NV_INDEX, sizeof(sub_cap),
                             sub_cap, &resp_size, resp);

#ifdef TPM_TRACE
    printf("TPM: get nv_data_public, return value = %08X\n", ret);
#endif
    if ( ret != TPM_SUCCESS ) {
        printf("TPM: fail to get public data of 0x%08X in TPM NV\n", index);
        return ret;
    }

#ifdef TPM_TRACE
    {
        printf("TPM: ");
        print_hex(NULL, resp, resp_size);
    }
#endif

    /* check size */
    if ( resp_size == 0 ) {
        printf("TPM: Index 0x%08X does not exist\n", index);
        return TPM_BADINDEX;
    }

    /* check index */
    offset = sizeof(tpm_structure_tag_t);
    LOAD_INTEGER(resp, offset, idx);
#ifdef TPM_TRACE
    printf("TPM: get index value = %08X\n", idx);
#endif

    if ( idx != index ) {
        printf("TPM: Index 0x%08X is not the one expected 0x%08X\n",
               idx, index);
        return TPM_BADINDEX;
    }

    if ( resp_size != sizeof(resp) ) {
        printf("TPM: public data size of Index 0x%08X responsed incorrect\n",
               index);
        return TPM_FAIL;
    }

    offset = 0;
    LOAD_NV_DATA_PUBLIC(resp, offset, pub);

    /*print_hex("  NV pub: ", pub, resp_size);*/

    return ret;
}


uint32_t tpm_save_state(uint32_t locality)
{
    uint32_t ret, offset, out_size;
    uint32_t retries = 0;

    do {
        offset = 0;
        out_size = 0;

        ret = tpm_submit_cmd(locality, TPM_ORD_SAVE_STATE, offset, &out_size);
        if ( retries == 0 )
            printf("TPM: save state, return value = %08X\n", ret);
        else if ( retries == 1 )
            printf("retrying command: .");
        else
            printf(".");

        if ( ret != TPM_RETRY )
            break;

        retries++;
        //ASSERT(false); // XXX need delay support
        //delay(100);
        //delay support; should probably end up using udelay (EMHF) or
        //environment specific delay routine
        printf("\nHalting, need delay support...");
        while(1);
    } while ( retries < MAX_SAVESTATE_RETRIES );
    if ( retries >= MAX_SAVESTATE_RETRIES )
        printf("TIMEOUT!");
    if ( retries > 0 )
        printf("\n");

    return ret;
}
