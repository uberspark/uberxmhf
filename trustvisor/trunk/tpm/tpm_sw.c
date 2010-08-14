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

/* tpm_sw.c routines to handle all software TPM related functions
 * Written for TrustVisor by Ning Qu
 */

#include <types.h>
#include <error.h>
#include <multiboot.h>
#include <string.h>
#include <print.h>
#include <svm.h>
#include <sha1.h>
#include <processor.h>
#include <visor.h>
#include <paging.h>
#include <heap.h>
#include <io.h>
#include <pci.h>
#include <dev.h>
#include <tpm.h>
#include <tpm_sw.h>
#include <scode.h>
#include <aes.h>
#include <rsa.h>
#include <arc4.h>
#include <malloc.h>
/*
   static u8 prngSeed[20]=
   {
   0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00,
   };
 */
/*
   u8 sealAesKey[16]=
   {
   0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00,
   };

   u8 sealHmacKey[20]=
   {
   0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00,
   };
 */

extern int scode_curr;
/* whitelist of all approved sensitive code regions */
extern whitelist_entry_t *whitelist;

/*TPM functions */
u32 TPM_PcrRead(u8* data, u32 num)
{  
	if (scode_curr < 0)
	{
		printf("SECURITY: try to use software TPM outside sensitive code DETECTED !! (rip %#x)\n",
				(u32)linux_vmcb->rip);
		return 1;
	}

	if (num > (TPM_PCR_NUM - 1))
	{
		printf("SECURITY: pcr num %d is not correct!!!\n", num);
		return 1;
	}
	DEBUG printf("DEBUG: PCR %d read, scode_curr %d\n", num, scode_curr);
	memcpy(data, whitelist[scode_curr].pcr + num*TPM_PCR_SIZE, TPM_PCR_SIZE);

	return TPM_SUCCESS;
}

/* function TPM_PcrWrite is not defined in tpm.h */
u32 TPM_PcrWrite(u8* data, u32 num)
{
	if (scode_curr < 0)
	{
		printf("SECURITY: try to use software TPM outside sensitive code DETECTED !! (rip %#x)\n",
				(u32)linux_vmcb->rip);
		return 1;
	}

	if (num > (TPM_PCR_NUM - 1))
	{
		printf("SECURITY: PCR num %d is too large\n", num);
		return 1;
	}
	DEBUG printf("DEBUG: PCR Write %d\n", num);
	memcpy(whitelist[scode_curr].pcr + num*TPM_PCR_SIZE, data, TPM_PCR_SIZE);

	DEBUG printf("DEBUG: now pcr %d value %d, %#x\n", num, 0, *(unsigned int*)(whitelist[scode_curr].pcr + num*TPM_PCR_SIZE));
	return TPM_SUCCESS;
}

/* Software TPM functions */
u32 stpm_pcrread(u8* value, u32 num)
{ 

	TPM_PcrRead(value, num);

	return 0;
}

u32 stpm_extend(u8* hash, u32 num)
{
	u8 C1[TPM_HASH_SIZE + TPM_PCR_SIZE];
	u8 H1[TPM_HASH_SIZE];
	int i;

	if (num > (TPM_PCR_NUM -1 ))
	{
		printf("SECURITY: PCR num %d is too large\n", num);
		printf("SECURITY: PCR Extend fail\n");
		return 0;
	}

	/*get c1*/
	TPM_PcrRead(C1, num);

	memcpy(C1+TPM_PCR_SIZE, hash, TPM_HASH_SIZE);

	/*get h1*/
	sha1_csum(C1, TPM_HASH_SIZE + TPM_PCR_SIZE, H1);

	/*write back*/
	TPM_PcrWrite(H1, num);
	DEBUG printf("DEBUG: TPM PCR[0] value:\nDEBUG: ");
	for(i=0;i<TPM_HASH_SIZE;i++) {
		DEBUG printf("%x ", H1[i]);
	}
	DEBUG printf("\n");

	return TPM_SUCCESS;
}

u32 stpm_seal(u8* pcrAtRelease, u8* input, u32 inlen, u8* output, u32* outlen)
{
	s32 len;
	u8* pdata;
	u8 iv[16]; /* initial iv for aes-cbc encryption */
	aes_context ctx;
	memset(iv, 0, 16);

	if (scode_curr < 0)
	{
		printf("SECURITY: try to use software TPM outside sensitive code DETECTED !! (rip %#x)\n",
				(u32)linux_vmcb->rip);
		return 1;
	}

	/* construct TPM_STORED_DATA structure in output */
	memcpy(output, pcrAtRelease, TPM_PCR_SIZE); /* PCR value at release */
	*((u32 *)(output + TPM_PCR_SIZE)) = inlen + 4 + TPM_HASH_SIZE; /* data len */
	pdata = output + TPM_PCR_SIZE + 4;
	sha1_hmac(whitelist[scode_curr].hmackey, 20, input, inlen, pdata);  /* hmac of input data */
	pdata = pdata + TPM_PCR_SIZE; 
	*((u32 *)pdata) = inlen;        /*input data length */
	memcpy(pdata + 4, input, inlen); /* input data */
	*outlen = inlen + TPM_PCR_SIZE + 4 + TPM_PCR_SIZE + 4;
	len = (s32)(*outlen);
	/* encrypt data using sealAesKey by AES-CBC mode */
	aes_setkey_enc(&ctx, whitelist[scode_curr].aeskey, TPM_AES_KEY_LEN);
	aes_crypt_cbc(&ctx, AES_ENCRYPT, len, iv, output, output); 

	return TPM_SUCCESS;
}

u32 stpm_unseal(u8* input, u32 inlen, u8* output, u32* outlen)
{
	u32 len;
	u8 hashdata[2*TPM_HASH_SIZE];
	u8 iv[16];
	aes_context ctx;
	int i;

	if (scode_curr < 0)
	{
		printf("SECURITY: try to use software TPM outside sensitive code DETECTED !! (rip %#x)\n",
				(u32)linux_vmcb->rip);
		return 1;
	}	

	memset(iv, 0, 16);

	/* decrypt data */
	aes_setkey_dec(&ctx,whitelist[scode_curr].aeskey, TPM_AES_KEY_LEN);
	aes_crypt_cbc(&ctx, AES_DECRYPT, (s32)inlen, iv, input, output);

	/* compare the current pcr (default pcr 0) with pcrHashAtRelease */
	if(memcmp(output, whitelist[scode_curr].pcr, TPM_PCR_SIZE))
	{
		DEBUG printf("DEBUG: sealed pcr:\nDEBUG: ");
		for(i=0;i<TPM_PCR_SIZE;i++) {
			DEBUG printf("%x ",output[i]);
		}
		DEBUG printf("\nDEBUG: current pcr:\nDEBUG: ");
		for(i=0;i<TPM_PCR_SIZE;i++) {
			DEBUG printf("%x ",whitelist[scode_curr].pcr[i]);
		}
		DEBUG printf("\n");
		/* unseal fail , not necessary to clean buffer, because the output is buffer in host */
		return TPM_DECRYPT_ERROR;
	}

	/* get data length */
	len = *((u32*)(output + TPM_PCR_SIZE + 4 + TPM_HASH_SIZE)); 
	/* get hmac of data */
	sha1_hmac(whitelist[scode_curr].hmackey, 20, output + TPM_PCR_SIZE + 4 + TPM_HASH_SIZE + 4, len, hashdata);

	/*compare the hmac*/
	if (memcmp(hashdata, output + TPM_PCR_SIZE + 4, TPM_HASH_SIZE))
	{
		printf("DEBUG: Unseal HMAC check fail\n");
		return TPM_DECRYPT_ERROR;
	}
	memcpy(output, output + 48, inlen - 48);  /* delete header */				  
	*outlen = inlen - 48;
	DEBUG printf("DEBUG: unseal TPM done\n");
	return TPM_SUCCESS;
}

/*
 * todo: get TPM_QUOTE_INFO, then sign it
 * input: externalnonce, get from external server to avoid replay attack
 * output: quote result and data length
 */
u32 stpm_quote(u8* externalnonce, u8* output, u32* outlen)
{
	int ret;
	u32 datalen;
	//unsigned char hash[TPM_HASH_SIZE];

	if (scode_curr < 0)
	{
		printf("SECURITY: try to use software TPM outside sensitive code DETECTED !! (rip %#x)\n",
				(u32)linux_vmcb->rip);
		return 1;
	}

	/* construct TPM_QUOTE_INFO in output */
	((u32 *)output)[0] = 0x00000101;  /* version information */
	((u32 *)output)[1] = 0x544f5551; /* 'QUOTE' */
	sha1_csum(whitelist[scode_curr].pcr, TPM_PCR_SIZE*TPM_PCR_NUM, output + 8); /* hash of pcr */
	//memcpy(output, whitelist[scode_curr].pcr, TPM_PCR_SIZE);
	memcpy(output + 8 + TPM_PCR_SIZE, externalnonce, TPM_NONCE_SIZE); /* 160 bits nonce */

	datalen = 8 + TPM_HASH_SIZE + TPM_NONCE_SIZE;

	/* sign the quoteInfo and add the signature to output 
	 * get the outlen
	 */
	//static_malloc_init();

	ret = tpm_pkcs1_sign(&g_rsa, datalen, output, (output + datalen));

	if(ret != 0)
	{
		printf("DEBUG: rsa sign fail\n");
		return 1;
	}

	*outlen = TPM_RSA_KEY_LEN + TPM_NONCE_SIZE + TPM_HASH_SIZE + 8;

	return TPM_SUCCESS; 
}

/**
 *
 */
u32 stpm_rand(u8* buffer, u32 numbytes)
{
	if (scode_curr < 0)
	{
		printf("SECURITY: try to use software TPM outside sensitive code DETECTED !! (rip %#x)\n",
				(u32)linux_vmcb->rip);
		return 1;
	}

	if(!whitelist[scode_curr].refillNo) { /* first one; initialize key */
		arc4_setup(&(whitelist[scode_curr].arc4_ctx), whitelist[scode_curr].randKey, STPM_RANDOM_BUFFER_SIZE);
	}

	memset(buffer, 0, 128);
	memcpy(buffer, &(whitelist[scode_curr].refillNo), sizeof(unsigned long long));
	arc4_crypt(&(whitelist[scode_curr].arc4_ctx), buffer, numbytes);
	whitelist[scode_curr].refillNo++;
	return numbytes;
}

