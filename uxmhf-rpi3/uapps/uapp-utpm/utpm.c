/*
 * utpm interface
 * adapted from trustvisor utpm by amit vasudevan (amitvasudevan@acm.org
 */

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

#include <xmhfcrypto.h>
#include <sha1.h>
#include <aes.h>
#include <hmac-sha1.h>

#include <utpm.h>

//////
// global data variables
//////
// keys for software TPM seal, unseal and quote operations
__attribute__((section(".data"))) uint8_t g_aeskey[TPM_AES_KEY_LEN_BYTES];
__attribute__((section(".data"))) uint8_t g_hmackey[TPM_HMAC_KEY_LEN];
//rsa_key g_rsa_key;



//////
// interface functions
//////


////// initialize master entropy
/**
 * This function is expected to only be called once during the life of
 * anything that uses this uTPM implementation.  This function will
 * need significant modification if we ever decide to support
 * arbitrarily many signing keys for uTPM instances.
 */
TPM_RESULT utpm_init_master_entropy(uint8_t *aeskey,
                                    uint8_t *hmackey,
                                    void /*rsa_context*/ *rsa) {
    if(!aeskey || !hmackey || !rsa) {
        return UTPM_ERR_INSUFFICIENT_ENTROPY;

    }

    memcpy(g_aeskey, aeskey, TPM_AES_KEY_LEN_BYTES);
    memcpy(g_hmackey, hmackey, TPM_HMAC_KEY_LEN);
    //memcpy(&g_rsa_key, rsa, sizeof(g_rsa_key));

    /* ensure libtomcrypto's math descriptor is initialized */
    //if (!ltc_mp.name) {
    //  ltc_mp = ltm_desc;
    //}

    return UTPM_SUCCESS;
}


////// initialize instance
void utpm_init_instance(utpm_master_state_t *utpm) {
    if(NULL == utpm) return;

    memset(utpm->pcr_bank, 0, TPM_PCR_SIZE*TPM_PCR_NUM);

}

////// PCR read
/* software tpm pcr read */
TPM_RESULT utpm_pcrread(TPM_DIGEST* pcr_value /* output */,
                        utpm_master_state_t *utpm, uint32_t pcr_num) /* inputs */
{
    if(!pcr_value || !utpm) { return UTPM_ERR_BAD_PARAM; }
    if(pcr_num >= TPM_PCR_NUM)  { return UTPM_ERR_PCR_OUT_OF_RANGE; }

	memcpy(pcr_value->value, utpm->pcr_bank[pcr_num].value, TPM_PCR_SIZE);
	return UTPM_SUCCESS;
}



////// PCR extend
/* software tpm pcr extend */
TPM_RESULT utpm_extend(TPM_DIGEST *measurement, utpm_master_state_t *utpm, uint32_t pcr_num)
{
    unsigned long outlen;
    int rv;

    if(!measurement || !utpm) { return UTPM_ERR_BAD_PARAM; }
    if(pcr_num >= TPM_PCR_NUM) { return UTPM_ERR_PCR_OUT_OF_RANGE; }

    _XDPRINTF_("utpm_extend: extending PCR %d\n", pcr_num);

    //print_hex("utpm_extend: PCR before: ", utpm->pcr_bank[pcr_num].value, TPM_HASH_SIZE);
    //print_hex("utpm_extend: measurement: ", measurement->value, TPM_HASH_SIZE);

    /* pcr = H( pcr || measurement) */
    outlen = sizeof(utpm->pcr_bank[pcr_num].value);
    rv = sha1_memory_multi( utpm->pcr_bank[pcr_num].value, &outlen,
                       utpm->pcr_bank[pcr_num].value, TPM_HASH_SIZE,
                       measurement->value, TPM_HASH_SIZE,
                            NULL, NULL);
    if (rv) {
      //abort();
    	return UTPM_ERR;
    }

    //print_hex("utpm_extend: PCR after: ", utpm->pcr_bank[pcr_num].value, TPM_HASH_SIZE);

	return UTPM_SUCCESS;
}


////// PCR SEAL
TPM_RESULT utpm_seal(utpm_master_state_t *utpm,
                     TPM_PCR_INFO *tpmPcrInfo,
                     uint8_t* input, uint32_t inlen,
                     uint8_t* output, uint32_t* outlen)
{

	uint32_t rv = 0;
	uint32_t outlen_beforepad;
	uint8_t* p;
	uint8_t *iv;
    uint32_t bytes_consumed_by_pcrInfo;
    symmetric_CBC cbc_ctx;
    TPM_PCR_INFO tpmPcrInfo_internal;
    uint8_t *plaintext = NULL;
    uint32_t bytes_of_entropy = 0;

    if(!utpm || !tpmPcrInfo || !input || !output || !outlen) {
		//dprintf(LOG_ERROR, "[TV] utpm_seal ERROR: !utpm || !tpmPcrInfo || !input || !output || !outlen\n");
        return 1;
    }

    //dprintf(LOG_TRACE, "[TV:utpm_seal] inlen %u, outlen (junk expected) %u, tpmPcrInfo %p\n", inlen, *outlen, tpmPcrInfo);
    //print_hex("  [TV:utpm_seal] tpmPcrInfo: ", (uint8_t*)tpmPcrInfo, sizeof(TPM_PCR_INFO));
    //print_hex("  [TV:utpm_seal] input:      ", input, inlen);
    //print_hex("  [TV:utpm_seal] g_hmackey:    ", g_hmackey, TPM_HASH_SIZE); /* XXX SECURITY */
    //print_hex("  [TV:utpm_seal] g_aeskey:     ", g_aeskey, TPM_AES_KEY_LEN_BYTES); /* XXX SECURITY */

    /**
     * Part 1: Populate digestAtCreation (only for tpmPcrInfo that selects 1+ PCRs).
     */
    if(0 != tpmPcrInfo->pcrSelection.sizeOfSelect) {
        /* The caller does not provide the DigestAtCreation component of
         * the tpmPcrInfo input parameter, so we must populate this
         * component of the TPM_PCR_INFO structure ourselves,
         * internally. */
        /* 1. make our own TPM_PCR_INFO and copy caller-specified values */
        rv = utpm_internal_memcpy_TPM_PCR_INFO(tpmPcrInfo,
                                               NULL,
                                               &bytes_consumed_by_pcrInfo);
        if(0 != rv) { return 1; }
        if(bytes_consumed_by_pcrInfo != sizeof(TPM_PCR_INFO)) {
            //dprintf(LOG_ERROR, "[TV:UTPM] bytes_consumed_by_pcrInfo (%d) != sizeof(TPM_PCR_INFO) (%d)\n",
            //        bytes_consumed_by_pcrInfo, sizeof(TPM_PCR_INFO));
            return 1;
        }
        rv = utpm_internal_memcpy_TPM_PCR_INFO(tpmPcrInfo,
                                               (uint8_t*)&tpmPcrInfo_internal,
                                               &bytes_consumed_by_pcrInfo);
        if(0 != rv) { return 1; }

		#if 0
        /* 2. overwrite digestAtCreation based on current PCR contents */
        rv = utpm_internal_digest_current_TpmPcrComposite(
            utpm,
            &tpmPcrInfo_internal.pcrSelection,
            &tpmPcrInfo_internal.digestAtCreation);
        if(0 != rv) { return 1; }
		#endif
    } else {
        tpmPcrInfo_internal.pcrSelection.sizeOfSelect = 0;
    }


#if 0
    /**
     * Part 2: Do the actual encryption
     */

    plaintext = malloc(inlen + 100); /* XXX figure out actual required size */
    // It's probably TPM_AES_KEY_LEN_BYTES + TPM_HASH_SIZE + sizeof(TPM_PCR_INFO)
    if(NULL == plaintext) {
        dprintf(LOG_ERROR, "ERROR: malloc FAILED\n");
        return 1;
    }

    p = iv = plaintext;

	/* 0. get IV */
    bytes_of_entropy = TPM_AES_KEY_LEN_BYTES;
	rand_bytes(iv, &bytes_of_entropy);
    if(TPM_AES_KEY_LEN_BYTES != bytes_of_entropy) {
        dprintf(LOG_ERROR, "ERROR: rand_bytes FAILED\n");
        return UTPM_ERR_INSUFFICIENT_ENTROPY;
    }
    memcpy(output, iv, TPM_AES_KEY_LEN_BYTES); /* Copy IV directly to output */
    p += TPM_AES_KEY_LEN_BYTES; /* IV */

    print_hex("  iv: ", iv, TPM_AES_KEY_LEN_BYTES);

	/* output = IV || AES-CBC(TPM_PCR_INFO (or 0x0000 if none selected) || input_len || input || PADDING) || HMAC( entire ciphertext including IV ) */
    /* 1a. TPM_PCR_SELECTION with 0 PCRs selected */
    if(0 == tpmPcrInfo_internal.pcrSelection.sizeOfSelect) { /* no PCRs selected */
        memcpy(p, &tpmPcrInfo_internal.pcrSelection.sizeOfSelect,
                sizeof(tpmPcrInfo_internal.pcrSelection.sizeOfSelect));
        print_hex(" tpmPcrInfo_internal.pcrSelection.sizeOfSelect: ", p,
                  sizeof(tpmPcrInfo_internal.pcrSelection.sizeOfSelect));
        p += sizeof(tpmPcrInfo_internal.pcrSelection.sizeOfSelect);
    }
    /* 1b. TPM_PCR_SELECTION with 1 or more PCRs selected */
    else {
        rv = utpm_internal_memcpy_TPM_PCR_INFO(&tpmPcrInfo_internal, p, &bytes_consumed_by_pcrInfo);
        if(0 != rv) { return 1; }
        print_hex("  tpmPcrInfo_internal: ",
                  (uint8_t*)&tpmPcrInfo_internal,
                  bytes_consumed_by_pcrInfo);
        p += bytes_consumed_by_pcrInfo;
    }
    /* 2. input_len */
	*((uint32_t *)p) = inlen;
    print_hex(" inlen: ", p, sizeof(uint32_t));
    p += sizeof(uint32_t);
    /* 3. actual input data */
	memcpy(p, input, inlen);
    print_hex(" input: ", p, inlen);
    p += inlen;

	/* 4. add padding */
	outlen_beforepad = (uint32_t)p - (uint32_t)plaintext;
	if ((outlen_beforepad & 0xF) != 0) {
		*outlen = (outlen_beforepad + TPM_AES_KEY_LEN_BYTES) & (~0xF);
	} else {
		*outlen = outlen_beforepad;
	}
	memset(p, 0, *outlen-outlen_beforepad);

    print_hex("padding: ", p, *outlen - outlen_beforepad);
    p += *outlen - outlen_beforepad;

    /* encrypt (1-4) data using g_aeskey in AES-CBC mode */
    if ( cbc_start( find_cipher( "aes"), iv, g_aeskey, TPM_AES_KEY_LEN_BYTES, 0, &cbc_ctx)) {
      abort();
    }

    print_hex(" plaintext (including IV) just prior to AES encrypt: ", plaintext, *outlen);
    if (cbc_encrypt( plaintext + TPM_AES_KEY_LEN_BYTES, /* skip IV */
                     output + TPM_AES_KEY_LEN_BYTES, /* don't clobber IV */
                     *outlen - TPM_AES_KEY_LEN_BYTES,
                     &cbc_ctx)) {
      abort();
    }
    if (cbc_done( &cbc_ctx)) {
      abort();
    }

    print_hex(" freshly encrypted ciphertext: ", output, *outlen);

	/* 5. compute and append hmac */
    HMAC_SHA1(g_hmackey, TPM_HASH_SIZE, output, *outlen, output + *outlen);
    print_hex("hmac: ", output + *outlen, TPM_HASH_SIZE);
    *outlen += TPM_HASH_SIZE; /* hmac */

    dprintf(LOG_TRACE, "*outlen = %d\n", *outlen);
    print_hex("ciphertext from utpm_seal: ", output, *outlen);

    /* Sanity checking output size */
    if(*outlen != utpm_seal_output_size(inlen, false)) {
        dprintf(LOG_ERROR, "\n\nERROR!!! *outlen(%d) != utpm_seal_output_size(%d)\n\n", *outlen,
                utpm_seal_output_size(inlen, false));
    }

    /* SECURITY: zero memory before freeing? */
    if(plaintext) { free(plaintext); plaintext = NULL; iv = NULL; }
#endif

	return rv;
}
