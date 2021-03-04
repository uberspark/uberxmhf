/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*
 * utpm interface
 * adapted from trustvisor utpm by amit vasudevan (amitvasudevan@acm.org
 */

//#include <types.h>
//#include <arm8-32.h>
//#include <bcm2837.h>
//#include <miniuart.h>
//#include <debug.h>

#include <uberspark/uobjrtl/crt/include/string.h>
#include <uberspark/uobjrtl/crypto/include/basedefs.h>
#include <uberspark/uobjrtl/crypto/include/hashes/sha1/sha1.h>
#include <uberspark/uobjrtl/crypto/include/ciphers/aes/aes.h>
#include <uberspark/uobjrtl/crypto/include/mac/hmacsha1/hmacsha1.h>

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/libutpm/utpm.h>
//#include <uberspark/include/uberspark.h>

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

    uberspark_uobjrtl_crt__memcpy(g_aeskey, aeskey, TPM_AES_KEY_LEN_BYTES);
    uberspark_uobjrtl_crt__memcpy(g_hmackey, hmackey, TPM_HMAC_KEY_LEN);
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

    uberspark_uobjrtl_crt__memset(utpm->pcr_bank, 0, TPM_PCR_SIZE*TPM_PCR_NUM);

}

////// PCR read
/* software tpm pcr read */
TPM_RESULT utpm_pcrread(TPM_DIGEST* pcr_value /* output */,
                        utpm_master_state_t *utpm, uint32_t pcr_num) /* inputs */
{
    if(!pcr_value || !utpm) { return UTPM_ERR_BAD_PARAM; }
    if(pcr_num >= TPM_PCR_NUM)  { return UTPM_ERR_PCR_OUT_OF_RANGE; }

	uberspark_uobjrtl_crt__memcpy(pcr_value->value, utpm->pcr_bank[pcr_num].value, TPM_PCR_SIZE);
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

    //_XDPRINTF_("utpm_extend: extending PCR %d\n", pcr_num);

    //print_hex("utpm_extend: PCR before: ", utpm->pcr_bank[pcr_num].value, TPM_HASH_SIZE);
    //print_hex("utpm_extend: measurement: ", measurement->value, TPM_HASH_SIZE);

    /* pcr = H( pcr || measurement) */
    outlen = sizeof(utpm->pcr_bank[pcr_num].value);
    rv = uberspark_uobjrtl_crypto__hashes_sha1__sha1_memory_multi( utpm->pcr_bank[pcr_num].value, &outlen,
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
    uint8_t buf_plaintext[MAX_TPM_SEAL_DATA_SIZE];
    uint8_t *plaintext = &buf_plaintext;
    uint32_t bytes_of_entropy = 0;
    unsigned long hmac_sha1_out_len;

    if(!utpm || !tpmPcrInfo || !input || !output || !outlen) {
		//dprintf(LOG_ERROR, "[TV] utpm_seal ERROR: !utpm || !tpmPcrInfo || !input || !output || !outlen\n");
        return 1;
    }

    //dprintf(LOG_TRACE, "[TV:utpm_seal] inlen %u, outlen (junk expected) %u, tpmPcrInfo %p\n", inlen, *outlen, tpmPcrInfo);
    //print_hex("  [TV:utpm_seal] tpmPcrInfo: ", (uint8_t*)tpmPcrInfo, sizeof(TPM_PCR_INFO));
    //print_hex("  [TV:utpm_seal] input:      ", input, inlen);
    //print_hex("  [TV:utpm_seal] g_hmackey:    ", g_hmackey, TPM_HASH_SIZE); /* XXX SECURITY */
    //print_hex("  [TV:utpm_seal] g_aeskey:     ", g_aeskey, TPM_AES_KEY_LEN_BYTES); /* XXX SECURITY */

	//_XDPRINTFSMP_("%s: %u\n", __func__, __LINE__);

    /**
     * Part 1: Populate digestAtCreation (only for tpmPcrInfo that selects 1+ PCRs).
     */
    if(0 != tpmPcrInfo->pcrSelection.sizeOfSelect) {
    	//_XDPRINTFSMP_("%s: %u\n", __func__, __LINE__);

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

        /* 2. overwrite digestAtCreation based on current PCR contents */
        rv = utpm_internal_digest_current_TpmPcrComposite(
            utpm,
            &tpmPcrInfo_internal.pcrSelection,
            &tpmPcrInfo_internal.digestAtCreation);
        if(0 != rv) { return 1; }
    } else {
        tpmPcrInfo_internal.pcrSelection.sizeOfSelect = 0;
    }

	//_XDPRINTFSMP_("%s: %u\n", __func__, __LINE__);


    /**
     * Part 2: Do the actual encryption
     */
    if ( (inlen+100) > MAX_TPM_SEAL_DATA_SIZE)
    	return 1;

	//_XDPRINTFSMP_("%s: %u\n", __func__, __LINE__);

    //plaintext = malloc(inlen + 100); /* XXX figure out actual required size */
    //// It's probably TPM_AES_KEY_LEN_BYTES + TPM_HASH_SIZE + sizeof(TPM_PCR_INFO)
    //if(NULL == plaintext) {
    //    dprintf(LOG_ERROR, "ERROR: malloc FAILED\n");
    //    return 1;
    //}


    p = iv = plaintext;

	/* 0. get IV */
    bytes_of_entropy = TPM_AES_KEY_LEN_BYTES;
	utpm_rand_bytes(iv, &bytes_of_entropy);
    if(TPM_AES_KEY_LEN_BYTES != bytes_of_entropy) {
        //dprintf(LOG_ERROR, "ERROR: rand_bytes FAILED\n");
        return UTPM_ERR_INSUFFICIENT_ENTROPY;
    }
    uberspark_uobjrtl_crt__memcpy(output, iv, TPM_AES_KEY_LEN_BYTES); /* Copy IV directly to output */
    p += TPM_AES_KEY_LEN_BYTES; /* IV */

    //print_hex("  iv: ", iv, TPM_AES_KEY_LEN_BYTES);

	//_XDPRINTFSMP_("%s: %u\n", __func__, __LINE__);


	/* output = IV || AES-CBC(TPM_PCR_INFO (or 0x0000 if none selected) || input_len || input || PADDING) || HMAC( entire ciphertext including IV ) */
    /* 1a. TPM_PCR_SELECTION with 0 PCRs selected */
    if(0 == tpmPcrInfo_internal.pcrSelection.sizeOfSelect) { /* no PCRs selected */
        uberspark_uobjrtl_crt__memcpy(p, &tpmPcrInfo_internal.pcrSelection.sizeOfSelect,
                sizeof(tpmPcrInfo_internal.pcrSelection.sizeOfSelect));
        //print_hex(" tpmPcrInfo_internal.pcrSelection.sizeOfSelect: ", p,
        //          sizeof(tpmPcrInfo_internal.pcrSelection.sizeOfSelect));
        p += sizeof(tpmPcrInfo_internal.pcrSelection.sizeOfSelect);
    	//_XDPRINTFSMP_("%s: %u\n", __func__, __LINE__);

    }
    /* 1b. TPM_PCR_SELECTION with 1 or more PCRs selected */
    else {
        rv = utpm_internal_memcpy_TPM_PCR_INFO(&tpmPcrInfo_internal, p, &bytes_consumed_by_pcrInfo);
        if(0 != rv) { return 1; }
        //print_hex("  tpmPcrInfo_internal: ",
        //          (uint8_t*)&tpmPcrInfo_internal,
        //          bytes_consumed_by_pcrInfo);
        p += bytes_consumed_by_pcrInfo;
    	//_XDPRINTFSMP_("%s: %u\n", __func__, __LINE__);

    }



    /* 2. input_len */
	*((uint32_t *)p) = inlen;
    //print_hex(" inlen: ", p, sizeof(uint32_t));
    p += sizeof(uint32_t);


    /* 3. actual input data */
	uberspark_uobjrtl_crt__memcpy(p, input, inlen);
    //print_hex(" input: ", p, inlen);
    p += inlen;

	//_XDPRINTFSMP_("%s: %u\n", __func__, __LINE__);

	/* 4. add padding */
	outlen_beforepad = (uint32_t)p - (uint32_t)plaintext;
	if ((outlen_beforepad & 0xF) != 0) {
		*outlen = (outlen_beforepad + TPM_AES_KEY_LEN_BYTES) & (~0xF);
	} else {
		*outlen = outlen_beforepad;
	}
	uberspark_uobjrtl_crt__memset(p, 0, *outlen-outlen_beforepad);

	//_XDPRINTFSMP_("%s: %u outlen_beforepad=%u, *outlen=%u\n", __func__, __LINE__,
	//		outlen_beforepad, *outlen);

    //print_hex("padding: ", p, *outlen - outlen_beforepad);
    p += *outlen - outlen_beforepad;


    /* encrypt (1-4) data using g_aeskey in AES-CBC mode */
    if ( uberspark_uobjrtl_crypto__ciphers_aes__rijndael_cbc_start( iv, g_aeskey, TPM_AES_KEY_LEN_BYTES, 0, &cbc_ctx)) {
      //abort();
    	return 1;
    }

	//_XDPRINTFSMP_("%s: %u\n", __func__, __LINE__);

    //print_hex(" plaintext (including IV) just prior to AES encrypt: ", plaintext, *outlen);
    if (uberspark_uobjrtl_crypto__ciphers_aes__rijndael_cbc_encrypt( plaintext + TPM_AES_KEY_LEN_BYTES, /* skip IV */
                     output + TPM_AES_KEY_LEN_BYTES, /* don't clobber IV */
                     *outlen - TPM_AES_KEY_LEN_BYTES,
                     &cbc_ctx)) {
      //abort();
    	return 1;
    }

	//_XDPRINTFSMP_("%s: %u\n", __func__, __LINE__);


    if (uberspark_uobjrtl_crypto__ciphers_aes__rijndael_cbc_done( &cbc_ctx)) {
      //abort();
    	return 1;
    }

    //print_hex(" freshly encrypted ciphertext: ", output, *outlen);

	//_XDPRINTFSMP_("%s: %u: *outlen=%u\n", __func__, __LINE__, *outlen);

	/* 5. compute and append hmac */
    //HMAC_SHA1(g_hmackey, TPM_HASH_SIZE, output, *outlen, output + *outlen);
    hmac_sha1_out_len = 20;
    if( uberspark_uobjrtl_crypto__mac_hmacsha1__hmac_sha1_memory(g_hmackey, TPM_HASH_SIZE, output, *outlen, output + *outlen, &hmac_sha1_out_len) )
    	return 1;

	//_XDPRINTFSMP_("%s: %u\n", __func__, __LINE__);

    //print_hex("hmac: ", output + *outlen, TPM_HASH_SIZE);
    *outlen += TPM_HASH_SIZE; /* hmac */


    //dprintf(LOG_TRACE, "*outlen = %d\n", *outlen);
    //print_hex("ciphertext from utpm_seal: ", output, *outlen);

    /* Sanity checking output size */
    if(*outlen != utpm_seal_output_size(inlen, false)) {
        //dprintf(LOG_ERROR, "\n\nERROR!!! *outlen(%d) != utpm_seal_output_size(%d)\n\n", *outlen,
        //        utpm_seal_output_size(inlen, false));
    	return 1;
    }

	//_XDPRINTFSMP_("%s: %u\n", __func__, __LINE__);

    //if(plaintext) { free(plaintext); plaintext = NULL; iv = NULL; }

	return rv;
}



////// PCR UNSEAL
TPM_RESULT utpm_unseal(utpm_master_state_t *utpm,
                       uint8_t* input, uint32_t inlen,
                       uint8_t* output, uint32_t* outlen,
                       TPM_COMPOSITE_HASH *digestAtCreation) /* out */
{
	uint8_t hmacCalculated[TPM_HASH_SIZE];
	uint32_t rv;
        symmetric_CBC cbc_ctx;
        unsigned long hmac_sha1_out_len;

    if(!utpm || !input || !output || !outlen || !digestAtCreation) { return 1; }

	/**
     * Recall from utpm_seal():
     * output = IV || AES-CBC(TPM_PCR_INFO || input_len || input || PADDING) || HMAC( entire ciphertext including IV )
     */

    /**
     * Step 1: Verify HMAC.  This ensures the sealed ciphertext has
     * not been modified and that it was sealed on this particular
     * instance of TrustVisor.
     */

    /* Ciphertext (input) length should be a multiple of the AES block size + HMAC size */
    if(0 != (inlen - TPM_HASH_SIZE) % TPM_AES_KEY_LEN_BYTES) {
        //dprintf(LOG_ERROR, "Unseal Input **Length FAILURE**: 0 != (inlen - TPM_HASH_SIZE) %% TPM_AES_KEY_LEN_BYTES\n");
        //dprintf(LOG_ERROR, "inlen %d, TPM_HASH_SIZE %d, TPM_AES_KEY_LEN_BYTES %d\n",
        //        inlen, TPM_HASH_SIZE, TPM_AES_KEY_LEN_BYTES);
        return 1;
    }

    /* HMAC should be the last TPM_HASH_SIZE bytes of the
     * input. Calculate its expected value based on the first (inlen -
     * TPM_HASH_SIZE) bytes of the input and compare against provided
     * value. */
    //HMAC_SHA1(g_hmackey, TPM_HASH_SIZE, input, inlen - TPM_HASH_SIZE, hmacCalculated);
    hmac_sha1_out_len = 20;
    if( uberspark_uobjrtl_crypto__mac_hmacsha1__hmac_sha1_memory(g_hmackey, TPM_HASH_SIZE, input, inlen - TPM_HASH_SIZE, hmacCalculated, &hmac_sha1_out_len) )
    	return 1;

    if(uberspark_uobjrtl_crt__memcmp(hmacCalculated, input + inlen - TPM_HASH_SIZE, TPM_HASH_SIZE)) {
        //dprintf(LOG_ERROR, "Unseal HMAC **INTEGRITY FAILURE**: memcmp(hmacCalculated, input + inlen - TPM_HASH_SIZE, TPM_HASH_SIZE)\n");
        //print_hex("  hmacCalculated: ", hmacCalculated, TPM_HASH_SIZE);
        //print_hex("  input + inlen - TPM_HASH_SIZE:" , input + inlen - TPM_HASH_SIZE, TPM_HASH_SIZE);
        return 1;
    }


    /**
     * Step 2. Decrypt data.  I cannot think of a reason why this
     * could ever fail if the above HMAC check was successful.
     */

    *outlen = inlen
        - TPM_AES_KEY_LEN_BYTES /* iv */
        - TPM_HASH_SIZE;        /* hmac */

    if (uberspark_uobjrtl_crypto__ciphers_aes__rijndael_cbc_start(
                   input, /* iv is at beginning of input */
                   g_aeskey, TPM_AES_KEY_LEN_BYTES,
                   0,
                   &cbc_ctx)) {
      //abort();
    	return 1;
    }
    if (uberspark_uobjrtl_crypto__ciphers_aes__rijndael_cbc_decrypt( input+TPM_AES_KEY_LEN_BYTES, /* offset to ciphertext just beyond iv */
                     output,
                     *outlen,
                     &cbc_ctx)) {
      //abort();
      return 1;
    }
    if (uberspark_uobjrtl_crypto__ciphers_aes__rijndael_cbc_done( &cbc_ctx)) {
      //abort();
    	return 1;
    }

    //print_hex("  Unsealed plaintext: ", output, *outlen);


    /**
     * Step 3. Verify that PCR values match.
     */

    /* 1. Determine which PCRs were included */
    /* 2. Create the TPM_PCR_COMPOSITE for those PCRs with their current values */
    /* 3. Compare the COMPOSITE_HASH with the one in the ciphertext. */

    /* plaintext contains [ TPM_PCR_INFO | plaintextLen | plaintext ] */
    { /* Separate logic for PCR checking since eventually it will
       * likely be library functionality (TODO). */
        uint8_t *p = output;
        TPM_PCR_INFO unsealedPcrInfo;
        uint32_t bytes_consumed_by_pcrInfo;
        uint32_t space_needed_for_composite = 0;
        uint8_t buf_currentPcrComposite[MAX_PCR_COMPOSITE_SIZE];
        uint8_t *currentPcrComposite = &buf_currentPcrComposite;
        TPM_COMPOSITE_HASH digestRightNow;


        /* 1. TPM_PCR_INFO */
        rv = utpm_internal_memcpy_TPM_PCR_INFO((TPM_PCR_INFO*)p, (uint8_t*)&unsealedPcrInfo, &bytes_consumed_by_pcrInfo);
        if(0 != rv) return rv;
        p += bytes_consumed_by_pcrInfo;
        //print_hex("  unsealedPcrInfo: ", (uint8_t*)&unsealedPcrInfo, bytes_consumed_by_pcrInfo);


        /* 1a. Handle the simple case where no PCRs are involved */
        if(bytes_consumed_by_pcrInfo <= sizeof(unsealedPcrInfo.pcrSelection.sizeOfSelect)) {
            //dprintf(LOG_TRACE, "  No PCRs selected.  No checking required.\n");
            uberspark_uobjrtl_crt__memset(digestAtCreation->value, 0, TPM_HASH_SIZE);
        }
        /* 1b. Verify that required PCR values match */
        else {

        	//print_hex("  unsealedPcrInfo.digestAtRelease: ", (uint8_t*)&unsealedPcrInfo.digestAtRelease, TPM_HASH_SIZE);

            /* 2. Create current PCR Composite digest, for use in compairing against digestAtRelease */
            rv = utpm_internal_allocate_and_populate_current_TpmPcrComposite(
                utpm,
                &unsealedPcrInfo.pcrSelection,
                currentPcrComposite,
                &space_needed_for_composite);
            if(rv != 0) {
                //dprintf(LOG_ERROR, "utpm_internal_allocate_and_populate_current_TpmPcrComposite FAILED\n");
                return 1;
            }
            //print_hex("  current PcrComposite: ", currentPcrComposite, space_needed_for_composite);


            /* 3. Composite hash */
            //sha1_buffer(currentPcrComposite, space_needed_for_composite, digestRightNow.value);
            uberspark_uobjrtl_crypto__hashes_sha1__sha1_memory(currentPcrComposite, space_needed_for_composite, digestRightNow.value, TPM_HASH_SIZE);

            //print_hex("  digestRightNow: ", digestRightNow.value, TPM_HASH_SIZE);

            if(0 != uberspark_uobjrtl_crt__memcmp(digestRightNow.value, unsealedPcrInfo.digestAtRelease.value, TPM_HASH_SIZE)) {
                //dprintf(LOG_ERROR, "0 != memcmp(digestRightNow.value, unsealedPcrInfo.digestAtRelease.value, TPM_HASH_SIZE)\n");
                rv = 1;
                goto out;
            }

            //dprintf(LOG_TRACE, "[TV:UTPM_UNSEAL] digestAtRelase MATCH; Unseal ALLOWED!\n");

            uberspark_uobjrtl_crt__memcpy(digestAtCreation->value, unsealedPcrInfo.digestAtCreation.value, TPM_HASH_SIZE);
        }
        /* 4. Reshuffle output buffer and strip padding so that only
         * the user's plaintext is returned. Buffer's contents: [
         * plaintextLen | plainText | padding ] */

        *outlen = *((uint32_t*)p);
        p += sizeof(uint32_t);
        uberspark_uobjrtl_crt__memcpy(output, p, *outlen);

      out:
        //if(currentPcrComposite) { free(currentPcrComposite); currentPcrComposite = NULL; }
	  	 (void)0;

    } /* END Separate logic for PCR checking. */

    return rv;
}
