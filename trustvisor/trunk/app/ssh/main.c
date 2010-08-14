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

/**                                                                           
 * main.c -  sample application code for trustvisor.
 *                                                                                                                              
 * Copyright (C) 2009 Yanlin Li                 
 *   
 * Abstract: 
 * Application code for TrustVisor including registering and unregistering secure sensitive code for TrustVisor.
 * The secure sensitive is in file scode.c and scode.h. 
 * The registering and unregistering function is copied from flicker.c in /trustvisor/app
 *
 * History:
 * (1) Created on 02/16/2009 by yanlli at cmu dot edu
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License v2.0 as published by
 * the Free Software Foundation.                                            
 *
 * This program is distributed in the hope that it will be useful,                                                             
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details. 
*/

#include <stdio.h>
#include <stdlib.h>
#include "scode.h"
#include "passwd.h"
#include "malloc.h"
#include "rsa.h"
#include "sha1.h"

//function scod_registration
//todo: register secure sensitive code
int scode_registration(unsigned int start, unsigned int size, unsigned int ssp, unsigned int params)
{
	int ret;

	printf("register sensitive code by vmmcall:\n");
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(VISOR_SCMD_REG), "b"(start), "c"(size), "d"(ssp), "S"(params));

	printf("after vmmcall, ret %d\n", ret);

}

// fucntion scode_unregistration
// todo: unregister secure sensitive code
int scode_unregistration(unsigned int start)
{
	int ret;

	printf("unregister sensitive code by vmmcall:\n");
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(VISOR_SCMD_UNREG), "b"(start));

	printf("after vmmcall, ret %d\n", ret);

}

int test_rsa(void)
{
  static_malloc_init();
  if(rsa_self_test(1) != 0)
  {
      printf("rsa test fail\n");
      return 1;
  }
  printf("RSA test success!\n");
  return 0;
}

int avtive_page(unsigned int addr, unsigned int page_num)
{
  unsigned int i, addrdata;
  unsigned int* paddr;
  /* active pages containing sensitive code */
  printf("active sensitive pages:");
  for (i = 0; i < page_num; i++)
  {
      paddr = addr + i*PAGE_SIZE + 10;
	  addrdata = *paddr;
	  printf("addr %#x, data %#x\n", (unsigned int)paddr, addrdata);
   }
  printf("done\n");
  return 0;
}
// function main
// todo: main function
int main(void)
{
    int debug_flag = 1;
	int i,ret;        
	int ssp;
        unsigned int saddr; /*sensitive code begin address*/
        unsigned int slen;
		unsigned int pminfo_addr; /* sensitive code parameter info address*/
		unsigned int page_num; 
		unsigned char out[20];
		struct scode_params_info params_info;
        /* variable for ssl client and server */
 		rsa_context rsa;
		unsigned int plainlen;
		unsigned int* seallen;
		unsigned char password[PASSWORD_SIZE];
		unsigned char nonce[TPM_NONCE_SIZE];
		unsigned char plaintext[TPM_RSA_KEY_SIZE];
        unsigned char ciphertext[TPM_RSA_KEY_SIZE];
		unsigned char pcrAtRelease[TPM_PCR_SIZE];
		unsigned char hash[TPM_HASH_SIZE];
	    unsigned char sealdata[SEAL_DATA_SIZE]; /* sealed private key, 80bytes key + 48bytes pcr and hmac */

		/* initialize*/
		for (i = 0; i < PASSWORD_SIZE; i++)
		   password[i] = i;
		printf("prepare nonce .... ");
		for (i = 0; i < TPM_NONCE_SIZE; i++)
		   nonce[i] = i*1;
		//memset(nonce, 60, TPM_NONCE_SIZE);
		printf("done\n");
        memset(plaintext, 0, TPM_RSA_KEY_SIZE);
		memset(ciphertext, 0, TPM_RSA_KEY_SIZE);
		memset(pcrAtRelease, 0, TPM_PCR_SIZE);
		memset(hash, 0, TPM_HASH_SIZE);
        memset(sealdata, 0, SEAL_DATA_SIZE);
		memset(&rsa, 0, sizeof(rsa_context));        
		
		if(test_rsa())
		{
		  printf("test RSA fail\n");
		  return 1;
		}
		
		printf("Get RSA Public Key .... ");
		if(rsa_get_key(&rsa))/* get the const key */
		{ 
		   printf("get RAS key fail\n");
		   return 1;
		}
		printf("done\n");
		
		/* encrypt {password, nonce} with public key */
        printf("encrypt password with public key .... ");
		plainlen = TPM_NONCE_SIZE + PASSWORD_SIZE;
		memcpy(plaintext, password, PASSWORD_SIZE);
		memcpy(plaintext + PASSWORD_SIZE, nonce, TPM_NONCE_SIZE);
		ret = rsa_pkcs1_encrypt(&rsa, 
		                        RSA_PUBLIC, plainlen,
								plaintext, ciphertext);
		if (ret != 0)
		{
		   printf("fail\n");
		   return 1;
		}
		printf("done\n");

        for (i = 0; i < 128/4; i++)
		   printf("%#x", ((unsigned int*)ciphertext)[i]);
        printf("...............finish\n");
		/* get hash of password */
		printf("hash of password .... ");
		sha1(password, PASSWORD_SIZE, hash);
		printf("done\n");

		printf("Now, prepare to register server's sensitive code ...\n");

		/*initialize*/
		page_num = 21;
		saddr = (unsigned int)scode_pcrread;
		slen = page_num*PAGE_SIZE;
		pminfo_addr = (unsigned int)&params_info;

        /*parameter marshalling*/
        params_info.params_num = 5;
        params_info.pm_str[0].type = PARAMS_TYPE_POINTER;  /* ciphertext */
        params_info.pm_str[0].size = TPM_RSA_KEY_SIZE/4;    /* int number */
        params_info.pm_str[1].type = PARAMS_TYPE_POINTER;  /* sealed data */
        params_info.pm_str[1].size = SEAL_DATA_SIZE/4;
        params_info.pm_str[2].type = PARAMS_TYPE_POINTER;  /* nonce */
        params_info.pm_str[2].size = TPM_NONCE_SIZE/4;
		params_info.pm_str[3].type = PARAMS_TYPE_POINTER;  /* hash of password */
		params_info.pm_str[3].size = TPM_HASH_SIZE/4;
		params_info.pm_str[4].type = PARAMS_TYPE_INTEGRE;  /* 0: seal private key; other: check password*/
        params_info.pm_str[4].size = 1; /* 1 int = 4 bytes*/

        /* active pages containing sensitive code */
		avtive_page(saddr, page_num);
		readpass(); /* stack is in the page containing readpass()*/
        
#if 1
        ssp = (((unsigned int)saddr  + slen) & ~(PAGE_SIZE - 1)) - 0x10;
	    printf("info: scode %#x, size %#x, stack %#x, pminfo %#x\n", saddr, slen, ssp, pminfo_addr);
	    scode_registration((unsigned int)saddr, slen, ssp, pminfo_addr);

#if 1  // 1: open scode; 0: clode scode
        printf("seal private key ... ");
        scode_sshserver(rsa.P.p, sealdata, nonce, hash, 0);
		printf("length %d\n", nonce[0]);
		printf("done\n");
        printf("check password ... \n");
		scode_sshserver(ciphertext, sealdata, nonce, hash, 1);
		printf("done\n");
        
		for (i = 0; i < PASSWORD_SIZE; i++)
        {
		  printf("password is %d\n", sealdata[i]);
		}

		for (i = 0; i < TPM_NONCE_SIZE; i++)
		  printf("nonce %d is %d\n", i, sealdata[PASSWORD_SIZE + i]);
#endif
	    scode_unregistration((unsigned int)saddr);

#endif

} // end of main()
