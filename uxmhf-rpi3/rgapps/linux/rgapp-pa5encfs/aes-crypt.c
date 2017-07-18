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

#include "aes-crypt.h"

#define BLOCKSIZE 1024
#define FAILURE 0
#define SUCCESS 1

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



#define ENCRYPT 1
#define DECRYPT 0
#define PASS_THROUGH (-1)

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


extern int do_crypt(FILE* in, FILE* out, int action, char* key_str){
    /* Local Vars */

    /* Buffers */
    //unsigned char inbuf[BLOCKSIZE];
	unsigned char *inbuf;
    int inlen;
    /* Allow enough space in output buffer for additional cipher block */
    //unsigned char outbuf[BLOCKSIZE];
    unsigned char *outbuf;
    int outlen;
    int writelen;

	symmetric_CBC cbc_ctx;

	//allocate memory
	if (posix_memalign(&inbuf, 4096, BLOCKSIZE) != 0){
	    //printf("%s: error: line %u\n", __FUNCTION__);
    	return 0;
	}
	if (posix_memalign(&outbuf, 4096, BLOCKSIZE) != 0){
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

		/* Init Engine */
		if( rijndael_cbc_start(aes_iv, aes_key, AES_KEY_LEN_BYTES, 0, &cbc_ctx) != CRYPT_OK )
			goto ERR_freeall;
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
    		goto ERR_freeall;
    	}


    	/* If in cipher mode, perform cipher transform on block */
    	if(action == ENCRYPT){
    		fprintf(stderr, "aes-crypt debug: at location: 4\n");

    	    if( rijndael_cbc_encrypt(inbuf, outbuf, inlen, &cbc_ctx) != CRYPT_OK)
    	    	goto ERR_freeall;

    	    outlen = inlen;
    		fprintf(stderr, "aes-crypt debug: at location: 5\n");

    	    if( rijndael_cbc_done( &cbc_ctx) != CRYPT_OK)
    	    	goto ERR_freeall;

    		fprintf(stderr, "aes-crypt debug: at location: 6\n");

    	}else if (action == DECRYPT){
    		fprintf(stderr, "aes-crypt debug: at location: 7\n");

    	    if( rijndael_cbc_decrypt(inbuf, outbuf, inlen, &cbc_ctx) != CRYPT_OK)
    	    	goto ERR_freeall;

    	    outlen = inlen;
    		fprintf(stderr, "aes-crypt debug: at location: 8\n");

    	    if( rijndael_cbc_done( &cbc_ctx) != CRYPT_OK)
    	    	goto ERR_freeall;

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
    		goto ERR_freeall;
    	}
    }	//end-for

	fprintf(stderr, "aes-crypt debug: at location: 12\n");
	free(inbuf);
	free(outbuf);
	return 1;

ERR_freeall:
	free(inbuf);
	free(outbuf);
	return 0;
}

