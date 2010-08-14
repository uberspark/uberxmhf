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
 * scode.c - secure sensitive code sample application code for trustvisor.
 *
 * Copyright (C) 2009 Yanlin Li
 *
 * Abstract:
 * This c file contains secure sensitive sample funtions 
 *
 * History:
 * (1) Created on 02/17/2009 by yanlli at cmu dot edu
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

#include "malloc.h"
#include "rsa.h"
#include "scode.h"
#include "sha1.h"


/**
 *  \brief                          ssl server
 *  
 *  \params mode                    0 : seal private key
 *                                  1 : check password
 *
 *  \params cipher_addr             mode 0: address of private key, length is 1024 bits
 *                                  mode 1: cipher text from client, length is 1024 bits
 *
 *  \params sealdata_addr           mode 0: seal result
 *
 *  \return value                   1 : nonce fail
 *                                  2 : hash fail
 *                                  0 : success
 */
int scode_sshserver(unsigned int cipher_addr, unsigned int sealdata_addr, 
                    unsigned int nonce_addr, unsigned int hash_addr, unsigned int mode)
{
  rsa_context rsa;
  unsigned char pcrAtRelease[TPM_PCR_SIZE];
  unsigned char hash[TPM_HASH_SIZE];
  unsigned char rsakey[TPM_RSA_KEY_SIZE];
  unsigned char plaintext[TPM_RSA_KEY_SIZE];
  unsigned char *nonce;
  unsigned char *externalnonce;
  unsigned char *externalhash;
  unsigned int passwdlen;
  unsigned int inlen, outlen; /* save the sealdata length in mode 0*/
  unsigned int i;
  /* mode 1, check password */
  if (mode != 0)
  {
    /* get RSA key (note: this is not correct steps, but just for test )*/
    rsa_get_key(&rsa);    
    /* unseal private key */
    inlen = TPM_RSA_KEY_SIZE + 48;
    scode_unseal(sealdata_addr, inlen, (unsigned int)rsakey, &outlen); 
	/* decrypt cipher_text */
    rsa_pkcs1_decrypt(&rsa, RSA_PRIVATE, &outlen, (unsigned char*)cipher_addr, sealdata_addr);
	nonce = sealdata_addr + PASSWORD_SIZE;
	externalnonce = (unsigned char*)nonce_addr;
	/* compare nonce */
	for (i = 0; i < TPM_NONCE_SIZE; i++)
	{
	   if (nonce[i] != externalnonce[i])
	   {
	      externalnonce[i] = 100;
	      return 1;
	   }
	}

	/* get hash of password  and compare hash */
    sha1(plaintext, PASSWORD_SIZE, hash);

	externalhash = (unsigned char*)hash_addr;

	for (i = 0; i < TPM_HASH_SIZE; i++)
	{
	   if (hash[i] != externalhash[i])
	   {
	     externalnonce[i] = 200;
	     return 2;
		}
	}

//	externalnonce[i]= 50;
  }
  else
  {
    /* mode 0, seal private key */
    /* get pcrAtRelease */
	scode_pcrextend(cipher_addr, TPM_RSA_KEY_SIZE); /* extend pcr with private key */
    scode_pcrread(pcrAtRelease);
    /* seal private key */
    scode_seal(pcrAtRelease, cipher_addr, TPM_RSA_KEY_SIZE, sealdata_addr, (unsigned int)&outlen);
	*((unsigned char*)nonce_addr) = outlen;  /* in mode 0, mode is also used as output, saving the sealdata length*/
  }

  return 0;
}




// hash it self and the extend the pcr
int shash(unsigned char* input, int inlen, unsigned char* out)
{
  int i;

  static_malloc_init();
  i = rsa_self_test(1);
  if (i != 0)
    return 1;

  unsigned char pcr[TPM_PCR_SIZE];
  sha1(input, inlen, out);
  scode_pcrextend(input, inlen);
  scode_pcrread((unsigned int)pcr);

  for (i = 0; i < TPM_PCR_SIZE; i++)
     out[i] = pcr[i];

  return 0;
}
//function int sadd5(int* value, int len)
// todo: output = value[0] + value[1]
//int RP3 sadd5(int* value, int len)
int sadd5(unsigned char* value, int len)
{
   int i_sum = 0;
   int i = 0;
   int ret;
   unsigned int bufaddr;
   unsigned int inaddr, inlen;
   unsigned char pcr[TPM_PCR_SIZE];
   unsigned char out[64];
   unsigned char unseal[64];
   unsigned char seal[32];
   unsigned int outlen;
   int ilen = len;
   
   for (i = 0; i < 32; i++)
     seal[i] = i;

   for (i = 0; i < len; i++)
   {   
      i_sum += value[i];
   }

   if (ilen != 0)
   {
      scode_pcrread((unsigned int)pcr);
	  inaddr = (unsigned int)scode_pcrread;
	  inlen = 0x200;
	  scode_pcrextend(inaddr, inlen);
	  scode_pcrread((unsigned int)pcr);
	  inaddr = (unsigned int)seal;
	  scode_seal((unsigned int)pcr, inaddr, 32, (unsigned int)out, &outlen);
      scode_unseal((unsigned int)out, outlen, (unsigned int)unseal, &inlen);	  
       value[0] = inlen;
	   value[1] = outlen;
       for (i = 2; i < 64; i++)
       {
          value[i] = unseal[i];
       }
   }
   return i_sum;
}


int scode_pcrread(unsigned int addr)
{
   int ret;
   __asm__ __volatile__(
                        "vmmcall\n\t"
						:"=a"(ret)
						: "a"(VISOR_STPM_PCRREAD), "b"(addr));
}

int scode_pcrextend(unsigned int addr, unsigned int len)
{
   int ret;
   __asm__ __volatile__(
                        "vmmcall\n\t"
						:"=a"(ret)
						: "a"(VISOR_STPM_EXTEND), "b"(addr), "c"(len));
}

int scode_seal(unsigned int pcrAtRelease_addr,
               unsigned int inaddr, unsigned int inlen,
               unsigned int outaddr, unsigned int outlen_addr)
{
  int ret;
  __asm__ __volatile__(
                        "vmmcall\n\t"
			:"=a"(ret)
			: "a"(VISOR_STPM_SEAL), "b"(inaddr), "c"(inlen), "d"(pcrAtRelease_addr), "S"(outaddr), "D"(outlen_addr));
}

int scode_unseal(unsigned int inaddr, unsigned int inlen,
                 unsigned int outaddr, unsigned int outlen_addr)
{
  int ret;
  __asm__ __volatile__(
                        "vmmcall\n\t"
			:"=a"(ret)
			: "a"(VISOR_STPM_UNSEAL), "b"(inaddr), "c"(inlen), "d"(outaddr), "S"(outlen_addr));
}

int scode_quote(unsigned int nonce_addr, unsigned int outaddr, unsigned int outlen_addr)
{
  int ret;
  __asm__ __volatile__(
                       "vmmcall\n\t"
					   :"=a"(ret)
					   :"a"(VISOR_STPM_QUOTE), "b"(nonce_addr), "c"(outaddr), "d"(outlen_addr));
}

//function int sadd(int)
//todo: output = input + 100;
int sadd(int value)
{
  value += 200;
  return value;
}


int FC ssub(int value)
{
  value += 100;
  return value;
}

/*function int sadd2(int a, int b)
 todo: output = a + b;
*/
int RP3 sadd2(int a, int b)
{
  int value;
  value = a + b;
  return value;
}

/*function int sadd3(int a, int b, int c)
  todo: output = a + b + c;
*/
int RP3 sadd3(int a, int b, int c)
{
  int value;
  value = a + b + c;
  return value;
}


/*function int sadd4(int a, int b, int c, int d)
 *   todo: output = a + b + c + d;
 *   */
int RP3 sadd4(int a, int b, int c, int d)
{
  int value;
  value = a + b + c + d;
  return value;
}


//function int readpass(void)
//todo: read password input and display it in terminal 
int readpassword(void) 
{
  struct termios ts, ots;                                                                         
  char passbuf[100]; 

  //get and save termios settings                                                                 
  tcgetattr(STDIN_FILENO, &ts);                                                                   
  ots = ts;                                                                                       
  //change termios settings                                                                       
  ts.c_lflag &= ~ECHO;                                                                            
  ts.c_lflag |= ECHONL;                                                                           
  tcsetattr(STDIN_FILENO, TCSAFLUSH, &ts);                                                        
  //check settings                                                                                
  tcgetattr(STDIN_FILENO, &ts);                                                                   
  if(ts.c_lflag & ECHO){                                                                          
    fprintf(stderr, "Fail to trun off echo\n");                                                
    tcsetattr(STDIN_FILENO, TCSANOW, &ots);                                                    
    exit(1);                                                                                   
  }                                                                                               
  //read and print password                                                                       
  printf("Please enter password:");                                                               
  fflush(stdout);                                                                                 
  fgets(passbuf, sizeof(passbuf), stdin);                                                         
  printf("read password: %s", passbuf);                                                           
  //reset the former termios settings                                                             
  tcsetattr(STDIN_FILENO, TCSANOW, &ots);
  
  return 0;                                                                                        
} // end of readpass(void)  
