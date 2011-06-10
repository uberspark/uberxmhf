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

/* utpm.c routines to handle all micro-TPM related functions
 * Written for TrustVisor by Ning Qu
 * Edited by Zongwei Zhou, Jonathan McCune for EMHF project
 */

#include  "./include/scode.h"
#include  "./include/utpm.h"
#include  "./include/aes.h"
#include  "./include/rsa.h"
#include  "./include/sha1.h"
#include  "./include/puttymem.h"

void utpm_init_internal(utpm_master_state_t *utpm) {
    if(NULL == utpm) return;

    vmemset(utpm->pcr_bank, 0, TPM_PCR_SIZE*TPM_PCR_NUM); 

}

/* software tpm pcr read */
TPM_RESULT utpm_pcrread(TPM_DIGEST* pcr_value /* output */,
                        utpm_master_state_t *utpm, uint32_t pcr_num) /* inputs */
{ 
    if(!pcr_value || !utpm) { return UTPM_ERR_BAD_PARAM; }
    if(pcr_num >= TPM_PCR_NUM)  { return UTPM_ERR_PCR_OUT_OF_RANGE; }

	vmemcpy(pcr_value->value, utpm->pcr_bank[pcr_num].value, TPM_PCR_SIZE);
	return UTPM_SUCCESS;
}

/* software tpm pcr extend */
TPM_RESULT utpm_extend(TPM_DIGEST *measurement, utpm_master_state_t *utpm, uint32_t pcr_num)
{
    TPM_DIGEST old_pcr_val;
    TPM_DIGEST new_pcr_val;
    uint32_t rv;
    sha1_context ctx;

    if(!measurement || !utpm) { return UTPM_ERR_BAD_PARAM; }
    if(pcr_num >= TPM_PCR_NUM) { return UTPM_ERR_PCR_OUT_OF_RANGE; }

    sha1_starts( &ctx );
    /* existing PCR value */
    sha1_update( &ctx, utpm->pcr_bank[pcr_num].value, TPM_HASH_SIZE);
    /* new measurement */
    sha1_update( &ctx, measurement->value, TPM_HASH_SIZE);
    /* write new PCR value */
    sha1_finish( &ctx, utpm->pcr_bank[pcr_num].value );

	return UTPM_SUCCESS;
}

/* FIXME: place this somewhere appropriate */
static inline uint32_t ntohl(uint32_t in) {
    uint8_t *s = (uint8_t *)&in;
    return (uint32_t)(s[0] << 24 | s[1] << 16 | s[2] << 8 | s[3]);
}

/**
 * Create the current TPM_COMPOSITE_DIGEST for uTPM PCR values
 * specified by tpmsel.
 *
 * Caller must vfree *tpm_pcr_composite.
 */
/**
 * TODO: Use this function to eliminate duplicated logic in utpm_quote().
 */
static uint32_t utpm_internal_allocate_and_populate_current_TpmCompositeHash(
    utpm_master_state_t *utpm,
    TPM_PCR_SELECTION *tpmsel,
    uint8_t **tpm_pcr_composite,
    uint32_t *space_needed_for_composite
    )
{
    uint32_t rv = 0;
    uint32_t i;
    sha1_context ctx;
    uint32_t num_pcrs_to_include = 0;
    uint8_t *p = NULL;
    
    if(!utpm || !tpmsel || !tpm_pcr_composite || !space_needed_for_composite) return 1;    

    dprintf(LOG_TRACE, "[TV:UTPM] %s: tpmsel->sizeOfSelect %d\n",
            __FUNCTION__, tpmsel->sizeOfSelect);
    print_hex("  tpmsel->pcrSelect: ", tpmsel->pcrSelect, tpmsel->sizeOfSelect);
    for(i=0; i<TPM_PCR_NUM; i++) {
        if(utpm_pcr_is_selected(tpmsel, i)) {
            num_pcrs_to_include++;
        }
        dprintf(LOG_TRACE, "    uPCR-%d: %s\n", i,
                utpm_pcr_is_selected(tpmsel, i) ? "included" : "excluded");
    }    

    /**
     * Construct TPM_COMPOSITE structure that will summarize the relevant PCR values
     */

    /* Allocate space for the necessary number of uPCR values */
    // TPM_PCR_COMPOSITE contains TPM_PCR_SELECTION + n*TPM_HASH_SIZE PCR values
    
    /* struct TPM_PCR_COMPOSITE {
         TPM_PCR_SELECTION select;
         uint32_t valueSize;
         [size_is(valueSize)] TPM_PCRVALUE pcrValue[];
       };
    */
    *space_needed_for_composite =
        sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect + /* TPM_PCR_COMPOSITE.select */
        sizeof(uint32_t) +                                    /* TPM_PCR_COMPOSITE.valueSize */
        num_pcrs_to_include * TPM_HASH_SIZE;                  /* TPM_PCR_COMPOSITE.pcrValue[] */

    dprintf(LOG_TRACE, "  sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect = %d\n",
            sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect);
    dprintf(LOG_TRACE, "  sizeof(uint32_t)                                    = %d\n",
            sizeof(uint32_t));
    dprintf(LOG_TRACE, "  num_pcrs_to_include * TPM_HASH_SIZE                 = %d\n",
            num_pcrs_to_include * TPM_HASH_SIZE);
    dprintf(LOG_TRACE, "  ---------------------------------------------------------\n");
    dprintf(LOG_TRACE, "  *space_needed_for_composite                         = %d\n",
            *space_needed_for_composite);
    
    if(NULL == (*tpm_pcr_composite = vmalloc(*space_needed_for_composite))) {
        dprintf(LOG_ERROR, "[TV:UTPM] vmalloc(%d) failed!\n", *space_needed_for_composite);
        return 1;
    }

    /** Populate TPM_COMPOSITE buffer **/
    p = *tpm_pcr_composite;
    /* 1. TPM_PCR_COMPOSITE.select */ 
    vmemcpy(p, tpmsel, sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect);
    p += sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect;
    /* 2. TPM_PCR_COMPOSITE.valueSize (big endian # of bytes (not # of PCRs)) */
    *((uint32_t*)p) = ntohl(num_pcrs_to_include*TPM_HASH_SIZE);
    p += sizeof(uint32_t);
    /* 3. TPM_PCR_COMPOSITE.pcrValue[] */
    for(i=0; i<TPM_PCR_NUM; i++) {
        if(utpm_pcr_is_selected(tpmsel, i)) {
            vmemcpy(p, utpm->pcr_bank[i].value, TPM_HASH_SIZE);
            dprintf(LOG_TRACE, "  PCR-%d: ", i);
            print_hex(NULL, p, TPM_HASH_SIZE);
            p += TPM_HASH_SIZE;
        }        
    }

    /* TODO: Assert */
    if((uint32_t)p-(uint32_t)(*tpm_pcr_composite) != *space_needed_for_composite) {
        dprintf(LOG_ERROR, "[TV:UTPM] ERROR! (uint32_t)p-(uint32_t)*tpm_pcr_composite "
                "!= space_needed_for_composite\n");
        rv = 1; /* FIXME: Indicate internal error */
        goto out;
    }
    
    print_hex(" TPM_PCR_COMPOSITE: ", *tpm_pcr_composite, *space_needed_for_composite);
  out:
    return rv;
    
}

#define TPM_AES_KEY_LEN_BYTES (TPM_AES_KEY_LEN/8)

TPM_RESULT utpm_seal(utpm_master_state_t *utpm,
                     TPM_PCR_INFO *tpmPcrInfo,
                     uint8_t* input, uint32_t inlen,
                     uint8_t* output, uint32_t* outlen,
                     uint8_t* hmackey, uint8_t* aeskey)
{
    uint32_t rv = 0;
	uint32_t outlen_beforepad;
	uint8_t* p;
	uint8_t *iv;
    uint8_t *currentPcrComposite = NULL;
    uint32_t space_needed_for_composite;
	aes_context ctx;
    TPM_PCR_INFO tpmPcrInfo_internal;
    TPM_DIGEST pcrInfoDigest;
    uint8_t *plaintext = NULL;
    if(!utpm || !tpmPcrInfo || !input || !output || !outlen || !hmackey || !aeskey) { return 1; }

    dprintf(LOG_TRACE, "[TV:utpm_seal] inlen %d, outlen %d\n", inlen, outlen);
    print_hex("  [TV:utpm_seal] tpmPcrInfo: ", (uint8_t*)tpmPcrInfo, sizeof(TPM_PCR_INFO));
    print_hex("  [TV:utpm_seal] input:      ", input, inlen);
    print_hex("  [TV:utpm_seal] hmackey:    ", hmackey, TPM_HASH_SIZE); /* XXX SECURITY */
    print_hex("  [TV:utpm_seal] aeskey:     ", aeskey, TPM_AES_KEY_LEN_BYTES); /* XXX SECURITY */
    
    /**
     * Part 1: Populate digestAtCreation (only for non-NULL tpmPcrInfo).
     */
    if(NULL != tpmPcrInfo) {
        /* The caller does not provide the DigestAtCreation component of
         * the tpmPcrInfo input parameter, so we must populate this
         * component of the TPM_PCR_INFO structure ourselves,
         * internally. */
        /* 1. make our own TPM_PCR_INFO and copy caller-specified values */
        vmemcpy((uint8_t*)&tpmPcrInfo_internal, tpmPcrInfo, sizeof(TPM_PCR_INFO));
        
        /* 2. overwrite digestAtCreation based on current PCR contents */
        rv = utpm_internal_allocate_and_populate_current_TpmCompositeHash(
            utpm,
            &tpmPcrInfo_internal.pcrSelection,
            &currentPcrComposite,
            &space_needed_for_composite);
        if(rv != 0) {
            dprintf(LOG_ERROR, "utpm_internal_allocate_and_populate_current_TpmCompositeHash FAILED\n");
            return 1;
        }
        
        sha1_csum(currentPcrComposite,
                  space_needed_for_composite,
                  tpmPcrInfo_internal.digestAtCreation.value);
        vfree(currentPcrComposite); currentPcrComposite = NULL;
        space_needed_for_composite = 0;

        /* 3. hash down the TPM_PCR_INFO structure into a single digest */
        sha1_csum((uint8_t*)&tpmPcrInfo_internal, sizeof(TPM_PCR_INFO), pcrInfoDigest.value);
    } else {
        /* Use digest of all 0's if no PCRs selected */
        vmemset(pcrInfoDigest.value, 0, TPM_HASH_SIZE);
    }
    /**
     * Part 2: Do the actual encryption
     */

    plaintext = vmalloc(inlen + 100); /* XXX figure out actual required size */
    // It's probably TPM_AES_KEY_LEN_BYTES + TPM_HASH_SIZE + sizeof(TPM_PCR_SELECTION)
    if(NULL == plaintext) {
        dprintf(LOG_ERROR, "ERROR: vmalloc FAILED\n");
        return 1;
    }
    
    p = iv = plaintext;

	/* 0. get IV */
	rand_bytes(iv, TPM_AES_KEY_LEN_BYTES);
    vmemcpy(output, iv, TPM_AES_KEY_LEN_BYTES); /* Copy IV directly to output */
    p += TPM_AES_KEY_LEN_BYTES; /* IV */

    print_hex("  iv: ", iv, TPM_AES_KEY_LEN_BYTES);
    
	/* output = IV || AES-CBC(TPM_PCR_SELECTION || PCR Composite hash || input_len || input || PADDING) || HMAC( entire ciphertext including IV ) */
    /* 1. TPM_PCR_SELECTION */
    vmemcpy(p, &tpmPcrInfo_internal.pcrSelection,
            sizeof(tpmPcrInfo_internal.pcrSelection.sizeOfSelect) + 
            tpmPcrInfo_internal.pcrSelection.sizeOfSelect);
    print_hex(" tpmPcrInfo_internal.pcrSelection: ", p,
            sizeof(tpmPcrInfo_internal.pcrSelection.sizeOfSelect) + 
            tpmPcrInfo_internal.pcrSelection.sizeOfSelect);
    p += sizeof(tpmPcrInfo_internal.pcrSelection.sizeOfSelect) + 
        tpmPcrInfo_internal.pcrSelection.sizeOfSelect;
    /* 2. PCR Composite hash */
	vmemcpy(p, pcrInfoDigest.value, TPM_HASH_SIZE); 
    print_hex(" pcrInfoDigest.value: ", p, TPM_HASH_SIZE);
    p += TPM_HASH_SIZE;    
    /* 3. input_len */
	*((uint32_t *)p) = inlen; 
    print_hex(" inlen: ", p, sizeof(uint32_t));
    p += sizeof(uint32_t);
    /* 4. actual input data */
	vmemcpy(p, input, inlen); 
    print_hex(" input: ", p, inlen);
    p += inlen;

	/* 5. add padding */
	outlen_beforepad = (uint32_t)p - (uint32_t)plaintext;
	if ((outlen_beforepad & 0xF) != 0) {
		*outlen = (outlen_beforepad + TPM_AES_KEY_LEN_BYTES) & (~0xF);
	} else {
		*outlen = outlen_beforepad;
	}
	vmemset(p, 0, *outlen-outlen_beforepad);
    print_hex("padding: ", p, *outlen - outlen_beforepad);
    p += *outlen - outlen_beforepad;
    
	/* encrypt (1-5) data using sealAesKey by AES-CBC mode */
	aes_setkey_enc(&ctx, aeskey, TPM_AES_KEY_LEN);
    print_hex(" plaintext (including IV) just prior to AES encrypt: ", plaintext, *outlen);
	aes_crypt_cbc(&ctx, AES_ENCRYPT, *outlen - TPM_AES_KEY_LEN_BYTES,
                  iv,
                  plaintext + TPM_AES_KEY_LEN_BYTES, /* skip IV */
                  output + TPM_AES_KEY_LEN_BYTES); /* don't clobber IV */

    print_hex(" freshly encrypted ciphertext: ", output, *outlen);
    
	/* 6. compute and append hmac */
    sha1_hmac(hmackey, TPM_HASH_SIZE, output, *outlen, output + *outlen);
    print_hex("hmac: ", output + *outlen, TPM_HASH_SIZE);    
    *outlen += TPM_HASH_SIZE; /* hmac */

    dprintf(LOG_TRACE, "*outlen = %d\n", *outlen);
    print_hex("ciphertext from utpm_seal: ", output, *outlen);
              
    /* FIXME: zero memory before freeing? */
    if(plaintext) { vfree(plaintext); plaintext = NULL; iv = NULL; } 
    
	return rv;
}


TPM_RESULT utpm_unseal(utpm_master_state_t *utpm,
                       uint8_t* input, uint32_t inlen,
                       uint8_t* output, uint32_t* outlen,
                       uint8_t* hmackey, uint8_t* aeskey)
{
	uint32_t len;
	uint8_t hashdata[TPM_HASH_SIZE];
	uint8_t hmacCalculated[TPM_HASH_SIZE];
	uint8_t iv[16];
	aes_context ctx;
	uint32_t i, rv;

    if(!utpm || !input || !output || !outlen || !hmackey || !aeskey) { return 1; }
    
	/**
     * Recall from utpm_seal():
     * output = IV || AES-CBC(TPM_PCR_SELECTION || PCR Composite hash || input_len || input || PADDING) || HMAC( entire ciphertext including IV )
     */

    /**
     * Step 1: Verify HMAC.  This ensures the sealed ciphertext has
     * not been modified and that it was sealed on this particular
     * instance of TrustVisor.
     */

    /* Ciphertext (input) length should be a multiple of the AES block size + HMAC size */
    if(0 != (inlen - TPM_HASH_SIZE) % TPM_AES_KEY_LEN_BYTES) {
        dprintf(LOG_ERROR, "Unseal Input **Length FAILURE**: 0 != (inlen - TPM_HASH_SIZE) % TPM_AES_KEY_LEN_BYTES\n");
        dprintf(LOG_ERROR, "inlen %d, TPM_HASH_SIZE %d, TPM_AES_KEY_LEN_BYTES %d\n",
                inlen, TPM_HASH_SIZE, TPM_AES_KEY_LEN_BYTES);
        return 1;
    }

    /* HMAC should be the last TPM_HASH_SIZE bytes of the
     * input. Calculate its expected value based on the first (inlen -
     * TPM_HASH_SIZE) bytes of the input and compare against provided
     * value. */
    sha1_hmac(hmackey, TPM_HASH_SIZE, input, inlen - TPM_HASH_SIZE, hmacCalculated);
    if(vmemcmp(hmacCalculated, input + inlen - TPM_HASH_SIZE, TPM_HASH_SIZE)) {
        dprintf(LOG_ERROR, "Unseal HMAC **INTEGRITY FAILURE**: vmemcmp(hmacCalculated, input + inlen - TPM_HASH_SIZE, TPM_HASH_SIZE)\n");
        print_hex("  hmacCalculated: ", hmacCalculated, TPM_HASH_SIZE);
        print_hex("  input + inlen - TPM_HASH_SIZE:" , input + inlen - TPM_HASH_SIZE, TPM_HASH_SIZE);
        return 1;
    }

    /**
     * Step 2. Decrypt data.  I cannot think of a reason why this
     * could ever fail if the above HMAC check was successful.
     */
    
    *outlen = inlen
        - TPM_AES_KEY_LEN_BYTES /* iv */
        - TPM_HASH_SIZE;        /* hmac */
    
	aes_setkey_dec(&ctx, aeskey, TPM_AES_KEY_LEN);
	aes_crypt_cbc(&ctx, AES_DECRYPT,
                  *outlen,
                  input /* iv comes first */,
                  input+TPM_AES_KEY_LEN_BYTES /* offset to ciphertext just beyond iv */,
                  output);


    print_hex("  Unsealed plaintext: ", output, *outlen);


    /**
     * Step 3. Verify that PCR values match.
     */

    /* 1. Determine which PCRs were included */
    /* 2. Create the TPM_PCR_COMPOSITE for those PCRs with their current values */
    /* 3. Compare the COMPOSITE_HASH with the one in the ciphertext. */

    /* plaintext contains [ TPM_PCR_SELECTION | TPM_COMPOSITE HASH | plaintextLen | plaintext ] */
    {
    uint8_t *p = output;
    TPM_PCR_SELECTION pcrSelection;
    uint32_t space_needed_for_composite = 0;
    uint8_t *currentPcrComposite = NULL;
    TPM_DIGEST pcrInfoDigest;
    
    /* 1. TPM_PCR_SELECTION */
    vmemcpy(&pcrSelection, output,
            sizeof(pcrSelection.sizeOfSelect) + ((TPM_PCR_SELECTION*)p)->sizeOfSelect);
    p += sizeof(pcrSelection.sizeOfSelect) + ((TPM_PCR_SELECTION*)p)->sizeOfSelect;    
    print_hex("  pcrSelection: ", (uint8_t*)&pcrSelection, (uint32_t)p - (uint32_t)output);

    /* 2. PCR Composite */
    rv = utpm_internal_allocate_and_populate_current_TpmCompositeHash(
        utpm,
        &pcrSelection,
        &currentPcrComposite,
        &space_needed_for_composite);
    if(rv != 0) {
        dprintf(LOG_ERROR, "utpm_internal_allocate_and_populate_current_TpmCompositeHash FAILED\n");
        return 1;
    }

    print_hex("  current PcrComposite: ", currentPcrComposite, space_needed_for_composite);
    
    /* 3. Composite hash */
    //sha1_csum((uint8_t*)&tpmPcrInfo_internal, sizeof(TPM_PCR_INFO), pcrInfoDigest.value);

    if(currentPcrComposite) { vfree(currentPcrComposite); currentPcrComposite = NULL; }
    }
        
    dprintf(LOG_ERROR, "PCR check UNIMPLEMENTED\n");
    return 1;
    

	//return 0;
}


TPM_RESULT utpm_seal_deprecated(uint8_t* pcrAtRelease, uint8_t* input, uint32_t inlen, uint8_t* output, uint32_t* outlen, uint8_t * hmackey, uint8_t * aeskey)
{
	s32 len;
	uint32_t outlen_beforepad;
	uint8_t* pdata;
	uint8_t iv[16]; 
	uint8_t confounder[TPM_CONFOUNDER_SIZE];
	uint8_t hashdata[TPM_HASH_SIZE];
	aes_context ctx;

	/* IV can be 0 because we have confounder */
	vmemset(iv, 0, 16);

	/* get a random confounder */
	rand_bytes(confounder, TPM_CONFOUNDER_SIZE);

	/* output = 
	 * AES-CBC(confounder || HMAC( entire message w/ zero HMAC field) || pcr || input_len || input || PADDING)
	 * */
	vmemcpy(output, confounder, TPM_CONFOUNDER_SIZE);
	vmemset(output+TPM_CONFOUNDER_SIZE, 0, TPM_HASH_SIZE);
	vmemcpy(output+TPM_CONFOUNDER_SIZE+TPM_HASH_SIZE, pcrAtRelease, TPM_PCR_SIZE); 
	pdata = output + TPM_CONFOUNDER_SIZE + TPM_HASH_SIZE + TPM_PCR_SIZE;
	*((uint32_t *)pdata) = inlen;
	vmemcpy(pdata + 4, input, inlen);

	/* add padding */
	outlen_beforepad = TPM_CONFOUNDER_SIZE + TPM_PCR_SIZE + TPM_HASH_SIZE + 4 + inlen ;
	if ((outlen_beforepad&0xF) != 0) {
		*outlen = (outlen_beforepad+16)&(~0xF);
	} else {
		*outlen = outlen_beforepad;
	}
	len = (s32)(*outlen);
	vmemset(output+outlen_beforepad, 0, len-outlen_beforepad);

	/* get HMAC of the entire message w/ zero HMAC field */
	sha1_hmac(hmackey, 20, output, len, hashdata);
	vmemcpy(output+TPM_CONFOUNDER_SIZE, hashdata, TPM_HASH_SIZE);
	
	/* encrypt data using sealAesKey by AES-CBC mode */
	aes_setkey_enc(&ctx, aeskey, TPM_AES_KEY_LEN);
	aes_crypt_cbc(&ctx, AES_ENCRYPT, len, iv, output, output); 

	return 0;
}

TPM_RESULT utpm_unseal_deprecated(utpm_master_state_t *utpm, uint8_t* input, uint32_t inlen, uint8_t* output, uint32_t* outlen, uint8_t * hmackey, uint8_t * aeskey)
{
	uint32_t len;
	uint8_t hashdata[TPM_HASH_SIZE];
	uint8_t oldhmac[TPM_HASH_SIZE];
	uint8_t iv[16];
	aes_context ctx;
	int i;

	vmemset(iv, 0, 16);

	/* decrypt data */
	aes_setkey_dec(&ctx,aeskey, TPM_AES_KEY_LEN);
	aes_crypt_cbc(&ctx, AES_DECRYPT, (s32)inlen, iv, input, output);

	/* compare the current pcr (default pcr 0) with pcrHashAtRelease */
    /* XXX TODO: this code implicitly uses PCR 0, and assumes that it
     * is the first thing inside the pcr_bank.  This is a Bad Thing.
     * Need to mature pcr_bank into an actual structure, teach
     * seal/unseal about identifying which PCRs to seal to, etc. */
	if(vmemcmp(output+TPM_CONFOUNDER_SIZE+TPM_HASH_SIZE, utpm->pcr_bank[0].value, TPM_PCR_SIZE))
	{
		printf("[TV] Unseal ERROR: wrong pcr value!\n");
		printf("[TV] sealed pcr:");
		for(i=0;i<TPM_PCR_SIZE;i++) {
			printf("%x ",output[i+TPM_CONFOUNDER_SIZE+TPM_HASH_SIZE]);
		}
		printf("\n[TV] current pcr:");
		for(i=0;i<TPM_PCR_SIZE;i++) {
			printf("%x ",utpm->pcr_bank[0].value[i]);
		}
		printf("\n");
		return 1;
	}

	/* copy hmac */ 
	vmemcpy(oldhmac, output+TPM_CONFOUNDER_SIZE, TPM_HASH_SIZE);

	/* zero HMAC field, and recalculate hmac of the message */
	vmemset(output+TPM_CONFOUNDER_SIZE, 0, TPM_HASH_SIZE);
	sha1_hmac(hmackey, 20, output, inlen, hashdata);

	/* compare the hmac */
	if (vmemcmp(hashdata, oldhmac, TPM_HASH_SIZE))
	{
		printf("[TV] Unseal ERROR: HMAC check fail\n");
		return 1;
	}

	len = *((uint32_t*)(output + TPM_CONFOUNDER_SIZE +TPM_PCR_SIZE + TPM_HASH_SIZE)); 
	vmemcpy(output, output + TPM_CONFOUNDER_SIZE + TPM_PCR_SIZE + TPM_HASH_SIZE + 4, len);
	*outlen = len;

	return 0;
}

/* Desired hypercall response-length semantics: Hypercall response
 * length parameter is both an input and output parameter (i.e.,
 * pointer to a uint32_t).  Caller presets it to the size of its
 * response buffer.  Hypercall resets it to the size of the true
 * response if the hypercall succeeds (i.e., buffer is big enough), or
 * to the required size if the hypercall fails because the response
 * buffer is too small. */
TPM_RESULT utpm_quote(TPM_NONCE* externalnonce, TPM_PCR_SELECTION* tpmsel, /* hypercall inputs */
                      uint8_t* output, uint32_t* outlen, /* hypercall outputs */
                      utpm_master_state_t *utpm, uint8_t* rsa) /* TrustVisor inputs */
{
    TPM_RESULT rv = 0; /* success */
    uint32_t i = 0;
    uint32_t num_pcrs_to_include_in_quote = 0;
    uint32_t space_needed_for_composite = 0;
    uint8_t *tpm_pcr_composite = NULL;
    uint8_t *p = NULL;
    TPM_QUOTE_INFO quote_info;    
    uint32_t required_output_size;

    printf("[TV:UTPM] utpm_quote invoked\n");

    if(!externalnonce || !tpmsel || !output || !outlen || !utpm || !rsa) {
        printf("[TV:UTPM] ERROR: NULL function parameter!\n");
        rv = 1; /* FIXME: Indicate invalid input parameter */
        goto out;
    }

    print_hex(" externalnonce: ", externalnonce->nonce, TPM_HASH_SIZE);

    dprintf(LOG_TRACE, "[TV:UTPM] utpm_quote: tpmsel->sizeOfSelect %d\n", tpmsel->sizeOfSelect);
    print_hex("   tpmsel->pcrSelect: ", tpmsel->pcrSelect, tpmsel->sizeOfSelect);
    for(i=0; i<2*TPM_PCR_NUM; i++) {
        if(utpm_pcr_is_selected(tpmsel, i)) {
            num_pcrs_to_include_in_quote++;
        }
        dprintf(LOG_TRACE, "  uPCR-%d: %s\n", i,
                utpm_pcr_is_selected(tpmsel, i) ? "included" : "excluded");
    }    

    /**
     * Construct TPM_COMPOSITE structure that will summarize the relevant PCR values
     */

    /* Allocate space for the necessary number of uPCR values */
    // TPM_PCR_COMPOSITE contains TPM_PCR_SELECTION + n*TPM_HASH_SIZE PCR values
    
    /* struct TPM_PCR_COMPOSITE {
         TPM_PCR_SELECTION select;
         uint32_t valueSize;
         [size_is(valueSize)] TPM_PCRVALUE pcrValue[];
       };
    */
    space_needed_for_composite =
        sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect + /* TPM_PCR_COMPOSITE.select */
        sizeof(uint32_t) +                                    /* TPM_PCR_COMPOSITE.valueSize */
        num_pcrs_to_include_in_quote * TPM_HASH_SIZE;             /* TPM_PCR_COMPOSITE.pcrValue[] */

    dprintf(LOG_TRACE, "sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect = %d\n",
            sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect);
    dprintf(LOG_TRACE, "sizeof(uint32_t)                                    = %d\n",
            sizeof(uint32_t));
    dprintf(LOG_TRACE, "num_pcrs_to_include_in_quote * TPM_HASH_SIZE        = %d\n",
            num_pcrs_to_include_in_quote * TPM_HASH_SIZE);
    dprintf(LOG_TRACE, "--------------------------------------------------------\n");
    dprintf(LOG_TRACE, "space_needed_for_composite                          = %d\n",
            space_needed_for_composite);
    
    if(NULL == (tpm_pcr_composite = vmalloc(space_needed_for_composite))) {
        dprintf(LOG_ERROR, "[TV:UTPM] vmalloc(%d) failed!\n", space_needed_for_composite);
        return 1;
    }

    /** Populate TPM_COMPOSITE buffer **/
    p = tpm_pcr_composite;
    /* 1. TPM_PCR_COMPOSITE.select */ 
    vmemcpy(p, tpmsel, sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect);
    p += sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect;
    /* 2. TPM_PCR_COMPOSITE.valueSize (big endian # of bytes (not # of PCRs)) */
    *((uint32_t*)p) = ntohl(num_pcrs_to_include_in_quote*TPM_HASH_SIZE);
    p += sizeof(uint32_t);
    /* 3. TPM_PCR_COMPOSITE.pcrValue[] */
    for(i=0; i<TPM_PCR_NUM; i++) {
        if(utpm_pcr_is_selected(tpmsel, i)) {
            vmemcpy(p, utpm->pcr_bank[i].value, TPM_HASH_SIZE);
            print_hex("     PCR: ", p, TPM_HASH_SIZE);
            p += TPM_HASH_SIZE;
        }        
    }

    /* TODO: Assert */
    if((uint32_t)p-(uint32_t)tpm_pcr_composite != space_needed_for_composite) {
        dprintf(LOG_ERROR, "[TV:UTPM] ERROR! (uint32_t)p-(uint32_t)tpm_pcr_composite "
                "!= space_needed_for_composite\n");
        rv = 1; /* FIXME: Indicate internal error */
        goto out;
    }
    
    print_hex(" TPM_PCR_COMPOSITE: ", tpm_pcr_composite, space_needed_for_composite);
    
    /**
     * Populate 4-element TPM_QUOTE_INFO structure which will be hashed and signed
     */

    /* 1) 1.1.0.0 for consistency w/ TPM 1.2 spec */
    *((uint32_t*)&quote_info.version) = 0x00000101; 
    /* 2) 'QUOT' */
    *((uint32_t*)quote_info.fixed) = 0x544f5551; 
    /* 3) SHA-1 hash of TPM_PCR_COMPOSITE */
    sha1_csum(tpm_pcr_composite, space_needed_for_composite, quote_info.digestValue.value);
    print_hex(" COMPOSITE_HASH: ", quote_info.digestValue.value, TPM_HASH_SIZE);
    /* 4) external nonce */
    vmemcpy(quote_info.externalData.nonce, externalnonce->nonce, TPM_HASH_SIZE);

    print_hex(" quote_info: ", (uint8_t*)&quote_info, sizeof(TPM_QUOTE_INFO));
    
    /**
     * Compute the signature and format the output buffer
     */

    /* Output buffer: [ TPM_PCR_COMPOSITE | sigSize | sig ] */
    required_output_size = space_needed_for_composite +
        sizeof(uint32_t) + TPM_RSA_KEY_LEN;

    if(required_output_size > *outlen) {
        dprintf(LOG_ERROR, "ERROR: required_output_size (%d) > *outlen (%d)\n",
                required_output_size, *outlen);
        *outlen = required_output_size;
        rv = 1; /* FIXME: Indicate insufficient output buffer size */
        goto out;
    }

    *outlen = required_output_size;
    dprintf(LOG_TRACE, "required_output_size = *outlen = %d\n", *outlen);
    
    p = output;
    vmemcpy(p, tpm_pcr_composite, space_needed_for_composite);
    p += space_needed_for_composite;
    *((uint32_t*)p) = TPM_RSA_KEY_LEN;
    p += sizeof(uint32_t);
    

	if ((rv = tpm_pkcs1_sign((rsa_context *)rsa,
                             sizeof(TPM_QUOTE_INFO),
                             (uint8_t*)&quote_info,
                             p)) != 0) {
		printf("[TV:UTPM] ERROR: tpm_pkcs1_sign FAILED\n");
		goto out;
	}

#if 0
    { /* FIXME: Temporarily inserted code to verify our own signature
       * to make sure it works! */
        TPM_DIGEST tmp;
        sha1_csum((uint8_t*)&quote_info, sizeof(TPM_QUOTE_INFO), tmp.value);
        print_hex("sha1(quote_info): ", tmp.value, TPM_HASH_SIZE);
        
        printf("rsa_pkcs1_verify = %s\n",
               rsa_pkcs1_verify((rsa_context *)rsa,
                                RSA_PUBLIC, RSA_SHA1, 20,
                                tmp.value, p) == 0 ? "SUCCESS" : "FAIL"
               );               
    }
#endif /* if 0 */
    
    dprintf(LOG_TRACE, "[TV:UTPM] Success!\n");
    
  out:
    if(tpm_pcr_composite) { vfree(tpm_pcr_composite); tpm_pcr_composite = NULL; }
    
    return 0;
}

/*
 * todo: get TPM_QUOTE_INFO, then sign it
 * input: externalnonce, get from external server to avoid replay attack
 * output: quote result and data length
 */
TPM_RESULT utpm_quote_deprecated(uint8_t* externalnonce, uint8_t* output, uint32_t* outlen,
                      utpm_master_state_t *utpm, uint8_t* tpmsel, uint32_t tpmsel_len, uint8_t* rsa )
{
	int ret;
	uint32_t i, idx;
	uint8_t* pdata;
	uint32_t datalen;

	/* construct TPM_QUOTE_INFO in output */
	((uint32_t *)output)[0] = 0x00000101;  /* version information */
	((uint32_t *)output)[1] = 0x544f5551; /* 'QUOTE' */

	/* add TPM PCR information */
	vmemcpy(output+8, tpmsel, tpmsel_len);
	datalen = 8 + tpmsel_len;
	pdata = output+datalen;
	for( i=0 ; i<*((uint32_t *)tpmsel) ; i++ )  {
		idx=*(((uint32_t *)tpmsel)+i+1);
		vmemcpy(pdata+i*TPM_PCR_SIZE, utpm->pcr_bank[idx].value, TPM_PCR_SIZE);
		datalen += TPM_PCR_SIZE;
	}
	
	/* add nonce */
	vmemcpy(output + datalen, externalnonce, TPM_NONCE_SIZE); 
	datalen += TPM_NONCE_SIZE;

	/* sign the quoteInfo and add the signature to output 
	 * get the outlen
	 */
	if (ret = tpm_pkcs1_sign((rsa_context *)rsa, datalen, output, (output + datalen)) != 0) {
		printf("[TV] Quote ERROR: rsa sign fail\n");
		return 1;
	}
	*outlen = TPM_RSA_KEY_LEN + datalen;

	return 0; 
}


/* get random bytes from software TPM */
/* XXX TODO: Make this look like an actual TPM command (return value
 * should simply be a status code) */
uint32_t utpm_rand(uint8_t* buffer, uint32_t numbytes)
{
	numbytes = rand_bytes(buffer, numbytes);

	return numbytes;
}

