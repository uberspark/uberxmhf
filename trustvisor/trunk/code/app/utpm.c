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


/* XXX TODO: "Sealing" should support binding to an arbitrary number
 * of uPCRs.  Where is the bit vector to select the uPCRs of
 * interest? */
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

/* FIXME: place this somewhere appropriate */
static inline uint32_t ntohl(uint32_t in) {
    uint8_t *s = (uint8_t *)&in;
    return (uint32_t)(s[0] << 24 | s[1] << 16 | s[2] << 8 | s[3]);
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
    uint32_t i;
    uint32_t num_pcrs_to_include_in_quote=0;
    uint32_t space_needed_for_composite;
    uint8_t *tpm_pcr_composite;
    uint8_t *p;
    printf("[TV:UTPM] utpm_quote invoked\n");

    if(!externalnonce || !tpmsel || !output || !outlen || !utpm || !rsa) {
        printf("[TV:UTPM] ERROR: NULL function parameter!\n");
        return 1;
    }

    if(*outlen < TPM_QUOTE_SIZE) {
        printf("[TV:UTPM] *outlen (%d) too small; try again with at least TPM_QUOTE_SIZE bytes\n",
               *outlen);
        *outlen = TPM_QUOTE_SIZE;
        return 1;
    }

	dprintf(LOG_TRACE, "[TV:UTPM] utpm_quote: externalnonce:\n    ", *outlen);
	for(i=0; i<sizeof(TPM_NONCE); i++) {
		dprintf(LOG_TRACE, "%x ", externalnonce->nonce[i]);
	}
	dprintf(LOG_TRACE, "\n");

    dprintf(LOG_TRACE, "[TV:UTPM] utpm_quote: tpmsel->sizeOfSelect %d\n", tpmsel->sizeOfSelect);
    print_hex("   tpmsel->pcrSelect: ", tpmsel->pcrSelect, tpmsel->sizeOfSelect);
    for(i=0; i<2*TPM_PCR_NUM; i++) {
        if(utpm_pcr_is_selected(tpmsel, i)) {
            num_pcrs_to_include_in_quote++;
        }
        dprintf(LOG_TRACE, "  uPCR-%d: %s\n", i,
                utpm_pcr_is_selected(tpmsel, i) ? "included" : "excluded");
    }
    
    dprintf(LOG_TRACE, "[TV:UTPM] utpm_quote: inputs look sane but I'm UNIMPLEMENTED\n");

    /* Populate with some dummy values to test marshalling, etc. */
    *outlen = TPM_QUOTE_SIZE;
    for(i=0; i<*outlen; i++) {
        output[i] = (uint8_t)i;
    }

    /**
     * Construct TPM_COMPOSITE structure that will summarize the relevant PCR values
     */

    /* Allocate space for the necessary number of uPCR values */
    // TPM_COMPOSITE contains TPM_PCR_SELECTION + n*TPM_HASH_SIZE PCR values
    
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

    // Populate TPM_COMPOSITE buffer
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
        goto out;
    }
    
    print_hex(" TPM_PCR_COMPOSITE: ", tpm_pcr_composite, space_needed_for_composite);
    
    /**
     * Construct TPM_QUOTE_INFO structure which will be signed and hashed
     */

  out:
    vfree(tpm_pcr_composite); tpm_pcr_composite = NULL;
    
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

