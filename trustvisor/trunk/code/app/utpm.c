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

/* software tpm pcr write (only called by utpm_extend) */
static TPM_RESULT utpm_internal_pcrwrite(u8* new_pcr_value, u8* pcr_bank, u32 pcr_num)
{
    /* Internal function; param sanity-checking should already be
     * done. Use ASSERTs just to be safe. */
    ASSERT(new_pcr_value != NULL);
    ASSERT(pcr_bank != NULL);
    ASSERT(pcr_num < TPM_PCR_NUM);
    
	vmemcpy(pcr_bank + pcr_num*TPM_PCR_SIZE, new_pcr_value, TPM_PCR_SIZE);
	return UTPM_SUCCESS;
}

/* software tpm pcr read */
TPM_RESULT utpm_pcrread(u8* pcr_value /* output */,
                        u8* pcr_bank, u32 pcr_num) /* inputs */
{ 
    if(!pcr_value || !pcr_bank) { return UTPM_ERR_BAD_PARAM; }
    if(pcr_num >= TPM_PCR_NUM)  { return UTPM_ERR_PCR_OUT_OF_RANGE; }

	vmemcpy(pcr_value, pcr_bank + pcr_num*TPM_PCR_SIZE, TPM_PCR_SIZE);
	return UTPM_SUCCESS;
}

/* software tpm pcr extend */
TPM_RESULT utpm_extend(u8* measurement, u8* pcr_bank, u32 pcr_num)
{
	u8 scratch[TPM_PCR_SIZE + TPM_HASH_SIZE];
	u8 new_pcr_val[TPM_HASH_SIZE];
    u32 rv;

    if(!measurement || !pcr_bank) { return UTPM_ERR_BAD_PARAM; }
    if(pcr_num >= TPM_PCR_NUM)    { return UTPM_ERR_PCR_OUT_OF_RANGE; }
    
	/* read old PCR value */
	if(UTPM_SUCCESS != (rv = utpm_pcrread(scratch, pcr_bank, pcr_num))) {
        return rv;
    }

	/* append measurement */
	vmemcpy(scratch+TPM_PCR_SIZE, measurement, TPM_HASH_SIZE);

	/* calculate new PCR value */
	sha1_csum(scratch, TPM_HASH_SIZE + TPM_PCR_SIZE, new_pcr_val);

	/* write back. skip error check due to simplicity. */
	utpm_internal_pcrwrite(new_pcr_val, pcr_bank, pcr_num);

	return UTPM_SUCCESS;
}


/* XXX TODO: "Sealing" should support binding to an arbitrary number
 * of uPCRs.  Where is the bit vector to select the uPCRs of
 * interest? */
TPM_RESULT utpm_seal(u8* pcrAtRelease, u8* input, u32 inlen, u8* output, u32* outlen, u8 * hmackey, u8 * aeskey)
{
	s32 len;
	u32 outlen_beforepad;
	u8* pdata;
	u8 iv[16]; 
	u8 confounder[TPM_CONFOUNDER_SIZE];
	u8 hashdata[TPM_HASH_SIZE];
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
	*((u32 *)pdata) = inlen;
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

TPM_RESULT utpm_unseal(u8 * pcr_bank, u8* input, u32 inlen, u8* output, u32* outlen, u8 * hmackey, u8 * aeskey)
{
	u32 len;
	u8 hashdata[TPM_HASH_SIZE];
	u8 oldhmac[TPM_HASH_SIZE];
	u8 iv[16];
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
	if(vmemcmp(output+TPM_CONFOUNDER_SIZE+TPM_HASH_SIZE, pcr_bank, TPM_PCR_SIZE))
	{
		printf("[TV] Unseal ERROR: wrong pcr value!\n");
		printf("[TV] sealed pcr:");
		for(i=0;i<TPM_PCR_SIZE;i++) {
			printf("%x ",output[i+TPM_CONFOUNDER_SIZE+TPM_HASH_SIZE]);
		}
		printf("\n[TV] current pcr:");
		for(i=0;i<TPM_PCR_SIZE;i++) {
			printf("%x ",pcr_bank[i]);
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

	len = *((u32*)(output + TPM_CONFOUNDER_SIZE +TPM_PCR_SIZE + TPM_HASH_SIZE)); 
	vmemcpy(output, output + TPM_CONFOUNDER_SIZE + TPM_PCR_SIZE + TPM_HASH_SIZE + 4, len);
	*outlen = len;

	return 0;
}

/*
 * todo: get TPM_QUOTE_INFO, then sign it
 * input: externalnonce, get from external server to avoid replay attack
 * output: quote result and data length
 */
TPM_RESULT utpm_quote(u8* externalnonce, u8* output, u32* outlen, u8* pcr_bank, u8* tpmsel, u32 tpmsel_len, u8* rsa )
{
	int ret;
	u32 i, idx;
	u8* pdata;
	u32 datalen;

	/* construct TPM_QUOTE_INFO in output */
	((u32 *)output)[0] = 0x00000101;  /* version information */
	((u32 *)output)[1] = 0x544f5551; /* 'QUOTE' */

	/* add TPM PCR information */
	vmemcpy(output+8, tpmsel, tpmsel_len);
	datalen = 8 + tpmsel_len;
	pdata = output+datalen;
	for( i=0 ; i<*((u32 *)tpmsel) ; i++ )  {
		idx=*(((u32 *)tpmsel)+i+1);
		vmemcpy(pdata+i*TPM_PCR_SIZE, pcr_bank+idx*TPM_PCR_SIZE, TPM_PCR_SIZE);
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
u32 utpm_rand(u8* buffer, u32 numbytes)
{
	numbytes = rand_bytes(buffer, numbytes);

	return numbytes;
}

