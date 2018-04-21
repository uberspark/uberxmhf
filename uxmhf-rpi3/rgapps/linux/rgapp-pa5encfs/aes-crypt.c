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

/* aes-crypt.c
 * High level function interface for performing AES encryption on FILE pointers
 * Uses OpenSSL libcrypto EVP API
 *
 * By Andy Sayler (www.andysayler.com)
 * Created  04/17/12
 * Modified 04/18/12
 *
 * Derived from OpenSSL.org EVP_Encrypt_* Manpage Examples
 * http://www.openssl.org/docs/crypto/EVP_EncryptInit.html#EXAMPLES
 *
 * With additional information from Saju Pillai's OpenSSL AES Example
 * http://saju.net.in/blog/?p=36
 * http://saju.net.in/code/misc/openssl_aes.c.txt
 *
 */

#include <pa5encfs.h>
#include "aes-crypt.h"


#if 0
extern int do_crypt(FILE* in, FILE* out, int action, char* key_str){
    /* Local Vars */

    /* Buffers */
    unsigned char inbuf[BLOCKSIZE];
    int inlen;
    /* Allow enough space in output buffer for additional cipher block */
    unsigned char outbuf[BLOCKSIZE + EVP_MAX_BLOCK_LENGTH];
    int outlen;
    int writelen;

    /* OpenSSL libcrypto vars */
    EVP_CIPHER_CTX ctx;
    unsigned char key[32];
    unsigned char iv[32];
    int nrounds = 5;
    
    /* tmp vars */
    int i;
    fprintf(stderr, "aes-crypt debug: at location 1\n");
    /* Setup Encryption Key and Cipher Engine if in cipher mode */
    if(action >= 0){
		fprintf(stderr, "aes-crypt debug: at location: 2\n");
		if(!key_str){
			fprintf(stderr, "aes-crypt debug: at location: 3\n");
			/* Error */
			fprintf(stderr, "Key_str must not be NULL\n");
			return 0;
		}

		/* Build Key from String */
		i = EVP_BytesToKey(EVP_aes_256_cbc(), EVP_sha1(), NULL,
				   (unsigned char*)key_str, strlen(key_str), nrounds, key, iv);

		if (i != 32) {
		  fprintf(stderr, "aes-crypt debug: at location: 4\n");
			/* Error */
			fprintf(stderr, "Key size is %d bits - should be 256 bits\n", i*8);
			return 0;
		}

		/* Init Engine */
		EVP_CIPHER_CTX_init(&ctx);
		EVP_CipherInit_ex(&ctx, EVP_aes_256_cbc(), NULL, key, iv, action);
    }    

    /* Loop through Input File*/
    for(;;){
    	/* Read Block */
    	inlen = fread(inbuf, sizeof(*inbuf), BLOCKSIZE, in);
    	if(inlen <= 0){
    		/* EOF -> Break Loop */
    		break;
    	}
	
    	/* If in cipher mode, perform cipher transform on block */
    	if(action >= 0){
    		fprintf(stderr, "aes-crypt debug: at location: 5\n");
    		if(!EVP_CipherUpdate(&ctx, outbuf, &outlen, inbuf, inlen))
    		{
    			fprintf(stderr, "aes-crypt debug: at location: 7\n");
    			/* Error */
    			EVP_CIPHER_CTX_cleanup(&ctx);
    			return 0;
    		}
    	}
    	/* If in pass-through mode. copy block as is */
    	else{
    		fprintf(stderr, "aes-crypt debug: at location: 8\n");
    		memcpy(outbuf, inbuf, inlen);
    		outlen = inlen;
    	}

    	/* Write Block */
    	writelen = fwrite(outbuf, sizeof(*outbuf), outlen, out);
    	if(writelen != outlen){
    		fprintf(stderr, "aes-crypt debug: at location: 9\n");
    		/* Error */
    		perror("fwrite error");
    		EVP_CIPHER_CTX_cleanup(&ctx);
    		return 0;
    	}
    }	//end-for
    
    /* If in cipher mode, handle necessary padding */
    if(action >= 0){
      fprintf(stderr, "aes-crypt debug: at location: 10\n");
      /* Handle remaining cipher block + padding */
      if(!EVP_CipherFinal_ex(&ctx, outbuf, &outlen))
	  {
	      fprintf(stderr, "aes-crypt debug: at location: 11\n");
	      /* Error */
	      EVP_CIPHER_CTX_cleanup(&ctx);
	      return 0;
	  }
      /* Write remainign cipher block + padding*/
      fwrite(outbuf, sizeof(*inbuf), outlen, out);
      EVP_CIPHER_CTX_cleanup(&ctx);
    }
    
    fprintf(stderr, "aes-crypt debug: at location: 12\n");
    /* Success */
    return 1;
}
#endif //0





#if 0
extern int do_crypt(FILE* in, FILE* out, int action, char* key_str){
    /* Local Vars */

    /* Buffers */
    unsigned char inbuf[BLOCKSIZE];
    int inlen;
    /* Allow enough space in output buffer for additional cipher block */
    unsigned char outbuf[BLOCKSIZE];
    int outlen;
    int writelen;

	symmetric_CBC cbc_ctx;

    //action can be ENCRYPT (1), DECRYPT (0) or PASS_THROUGH (-1)

    fprintf(stderr, "aes-crypt debug: at location 1\n");

    /* Setup Encryption Key and Cipher Engine if in cipher mode */
    if(action == ENCRYPT || action == DECRYPT){
		fprintf(stderr, "aes-crypt debug: at location: 2\n");

		if(!key_str){
			fprintf(stderr, "aes-crypt debug: at location: 3\n");
			/* Error */
			fprintf(stderr, "Key_str must not be NULL\n");
			return 0;
		}

		/* Build Key from String */
		//TBD

		/* Init Engine */
		if( rijndael_cbc_start(aes_iv, aes_key, AES_KEY_LEN_BYTES, 0, &cbc_ctx) != CRYPT_OK )
			return 0;
    }

    /* Loop through Input File*/
    for(;;){
    	/* Read Block */
    	inlen = fread(inbuf, sizeof(*inbuf), BLOCKSIZE, in);
    	if(inlen <= 0){
    		/* EOF -> Break Loop */
    		break;
    	}

    	//sanity check inlen is multiple of AES block length (16 bytes)
    	if( inlen % 16 ){
    		fprintf(stderr, "aes-crypt debug: at location: 1.1\n");
    		return 0;
    	}


    	/* If in cipher mode, perform cipher transform on block */
    	if(action == ENCRYPT){
    		fprintf(stderr, "aes-crypt debug: at location: 4\n");

    	    if( rijndael_cbc_encrypt(inbuf, outbuf, inlen, &cbc_ctx) != CRYPT_OK)
    	    	return 0;

    	    outlen = inlen;
    		fprintf(stderr, "aes-crypt debug: at location: 5\n");

    	    if( rijndael_cbc_done( &cbc_ctx) != CRYPT_OK)
    	    	return 0;

    		fprintf(stderr, "aes-crypt debug: at location: 6\n");

    	}else if (action == DECRYPT){
    		fprintf(stderr, "aes-crypt debug: at location: 7\n");

    	    if( rijndael_cbc_decrypt(inbuf, outbuf, inlen, &cbc_ctx) != CRYPT_OK)
    	    	return 0;

    	    outlen = inlen;
    		fprintf(stderr, "aes-crypt debug: at location: 8\n");

    	    if( rijndael_cbc_done( &cbc_ctx) != CRYPT_OK)
    	    	return 0;

    		fprintf(stderr, "aes-crypt debug: at location: 9\n");

    	}else{
    		/* If in pass-through mode. copy block as is */
    		fprintf(stderr, "aes-crypt debug: at location: 10\n");
    		memcpy(outbuf, inbuf, inlen);
    		outlen = inlen;
    	}

    	/* Write Block */
    	writelen = fwrite(outbuf, sizeof(*outbuf), outlen, out);
    	if(writelen != outlen){
    		fprintf(stderr, "aes-crypt debug: at location: 11\n");
    		/* Error */
    		perror("fwrite error");
    		return 0;
    	}
    }	//end-for

	fprintf(stderr, "aes-crypt debug: at location: 12\n");

    return 1;
}
#endif



#if 0
//////
// back-end functions
//////
/*
	do_crypt using libxmhfcrypto aes primitive
	aeskey of size TPM_AES_KEY_LEN_BYTES (16)
	iv of size TPM_AES_KEY_LEN_BYTES (16) which is random
	cbc_start
	cbc_encrypt
	cbc_done
 */
uint8_t aes_iv[AES_KEY_LEN_BYTES] =
	{
			0x1a, 0x2a, 0x3a, 0x4a, 0x5a, 0x6a, 0x7a, 0x8a,
			0x1b, 0x2b, 0x3b, 0x4b, 0x5b, 0x6b, 0x7b, 0x8b
	};
uint8_t aes_key[AES_KEY_LEN_BYTES] =
	{
			0xfa, 0xea, 0xda, 0xca, 0xba, 0xaa, 0x9a, 0x8a,
			0xfb, 0xeb, 0xdb, 0xcb, 0xbb, 0xab, 0x9b, 0x8b
	};

symmetric_CBC cbc_ctx;

//returns 0 on fail
void do_crypt_start(pa5encfs_param_t *ep){
	/* Init Engine */
	if( rijndael_cbc_start(aes_iv, aes_key, AES_KEY_LEN_BYTES, 0, &cbc_ctx) != CRYPT_OK )
		ep->result = 0;
	else
		ep->result = 1;
}

//returns 0 on fail
void do_crypt_encrypt(pa5encfs_param_t *ep){
	if( rijndael_cbc_encrypt(ep->inbuf, ep->outbuf, ep->inlen, &cbc_ctx) != CRYPT_OK)
		ep->result=0;
	else
		ep->result=1;
}

//returns 0 on fail
void do_crypt_decrypt(pa5encfs_param_t *ep){
    if( rijndael_cbc_decrypt(ep->inbuf, ep->outbuf, ep->inlen, &cbc_ctx) != CRYPT_OK)
    	ep->result=0;
	else
		ep->result=1;
}

//returns 0 on fail
void do_crypt_done(pa5encfs_param_t *ep){
    if( rijndael_cbc_done( &cbc_ctx) != CRYPT_OK)
    	ep->result=0;
	else
		ep->result=1;
}



//////
#endif


//////
// back-end functions
//////
/*
	do_crypt using libxmhfcrypto aes primitive
	aeskey of size TPM_AES_KEY_LEN_BYTES (16)
	iv of size TPM_AES_KEY_LEN_BYTES (16) which is random
	cbc_start
	cbc_encrypt
	cbc_done
 */
uint8_t aes_iv[AES_KEY_LEN_BYTES] =
	{
			0x1a, 0x2a, 0x3a, 0x4a, 0x5a, 0x6a, 0x7a, 0x8a,
			0x1b, 0x2b, 0x3b, 0x4b, 0x5b, 0x6b, 0x7b, 0x8b
	};
uint8_t aes_key[AES_KEY_LEN_BYTES] =
	{
			0xfa, 0xea, 0xda, 0xca, 0xba, 0xaa, 0x9a, 0x8a,
			0xfb, 0xeb, 0xdb, 0xcb, 0xbb, 0xab, 0x9b, 0x8b
	};

symmetric_CBC cbc_ctx;

//returns 0 on fail
void do_crypt_start(pa5encfs_param_t *ep){
    if(!uhcall(UAPP_PA5ENCFS_FUNCTION_START, ep, sizeof(pa5encfs_param_t)))
    	fprintf(stderr, "hypercall FAILED\n");
    else
    	fprintf(stderr, "hypercall SUCCESS\n");
}

//returns 0 on fail
void do_crypt_encrypt(pa5encfs_param_t *ep){
    if(!uhcall(UAPP_PA5ENCFS_FUNCTION_ENCRYPT, ep, sizeof(pa5encfs_param_t)))
    	fprintf(stderr, "hypercall FAILED\n");
    else
    	fprintf(stderr, "hypercall SUCCESS\n");
}

//returns 0 on fail
void do_crypt_decrypt(pa5encfs_param_t *ep){
    if(!uhcall(UAPP_PA5ENCFS_FUNCTION_DECRYPT, ep, sizeof(pa5encfs_param_t)))
    	fprintf(stderr, "hypercall FAILED\n");
    else
    	fprintf(stderr, "hypercall SUCCESS\n");
}

//returns 0 on fail
void do_crypt_done(pa5encfs_param_t *ep){
    if(!uhcall(UAPP_PA5ENCFS_FUNCTION_DONE, ep, sizeof(pa5encfs_param_t)))
    	fprintf(stderr, "hypercall FAILED\n");
    else
    	fprintf(stderr, "hypercall SUCCESS\n");
}



//////



extern int do_crypt(FILE* in, FILE* out, int action, char* key_str){

	/* Local Vars */
    pa5encfs_param_t *ep;


	//allocate memory
	if (posix_memalign(&ep, 4096, sizeof(pa5encfs_param_t)) != 0){
	    //printf("%s: error: line %u\n", __FUNCTION__);
    	return 0;
	}


    //action can be ENCRYPT (1), DECRYPT (0) or PASS_THROUGH (-1)

    fprintf(stderr, "aes-crypt debug: at location 1\n");

    /* Setup Encryption Key and Cipher Engine if in cipher mode */
    if(action == ENCRYPT || action == DECRYPT){
		fprintf(stderr, "aes-crypt debug: at location: 2\n");

		if(!key_str){
			fprintf(stderr, "aes-crypt debug: at location: 3\n");
			/* Error */
			fprintf(stderr, "Key_str must not be NULL\n");
			goto ERR_freeall;
		}

		/* Build Key from String */
		//TBD

		do_crypt_start(ep);
		if(!ep->result)
			goto ERR_freeall;
    }

    /* Loop through Input File*/
    for(;;){
    	/* Read Block */
    	ep->inlen = fread(ep->inbuf, sizeof(unsigned char), BLOCKSIZE, in);
    	if(ep->inlen <= 0){
    		/* EOF -> Break Loop */
    		break;
    	}

    	//sanity check inlen is multiple of AES block length (16 bytes)
    	if( ep->inlen % 16 ){
    		fprintf(stderr, "aes-crypt debug: at location: 1.1\n");
    		goto ERR_freeall;
    	}


    	/* If in cipher mode, perform cipher transform on block */
    	if(action == ENCRYPT){
    		fprintf(stderr, "aes-crypt debug: at location: 4\n");

    	    do_crypt_encrypt(ep);
    	    if(!ep->result)
    	    	goto ERR_freeall;

    	    ep->outlen = ep->inlen;
    		fprintf(stderr, "aes-crypt debug: at location: 5\n");

    	    do_crypt_done(ep);
    	    if(!ep->result)
    	    	goto ERR_freeall;


    		fprintf(stderr, "aes-crypt debug: at location: 6\n");

    	}else if (action == DECRYPT){
    		fprintf(stderr, "aes-crypt debug: at location: 7\n");

    	    do_crypt_decrypt(ep);
    	    if(!ep->result)
    	    	goto ERR_freeall;

    	    ep->outlen = ep->inlen;
    		fprintf(stderr, "aes-crypt debug: at location: 8\n");

    	    do_crypt_done(ep);
    	    if(!ep->result)
    	    	goto ERR_freeall;

    		fprintf(stderr, "aes-crypt debug: at location: 9\n");

    	}else{
    		/* If in pass-through mode. copy block as is */
    		fprintf(stderr, "aes-crypt debug: at location: 10\n");
    		memcpy(ep->outbuf, ep->inbuf, ep->inlen);
    		ep->outlen = ep->inlen;
    	}

    	/* Write Block */
    	ep->writelen = fwrite(ep->outbuf, sizeof(unsigned char), ep->outlen, out);
    	if(ep->writelen != ep->outlen){
    		fprintf(stderr, "aes-crypt debug: at location: 11\n");
    		/* Error */
    		perror("fwrite error");
    		goto ERR_freeall;
    	}
    }	//end-for

	fprintf(stderr, "aes-crypt debug: at location: 12\n");
	free(ep);
	return 1;

ERR_freeall:
	free(ep);
	return 0;
}

