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

/* *******************************************************************************
 * Main Goal: protect HTTPS web server private key
 * 
 * System Architecture:
 * 		SSCB 1 -> pending for certificate -> SSCB 2...n
 *
 * SSCB 1:
 * 		1) generate a private key and certificate request when we bootstrap HTTPS server
 * 		2) seal the private key for SSCB 1 and store the sealed data in a file for recovery
 * 		3) seal the private key for SSCB 2 and pass the sealed data to SSCB 2
 * 		4) output the certicate request 
 *
 * pending for certificate:
 * 		Administrator use the certificate req from SSCB 1 to apply for a real certificate from CA
 * 		Once he/she get the certificate, put it in a specific file so that the web server can detect it
 *
 * SSCB 2:
 * 		1) unseal the private key using the sealed data from SSCB 1
 * 		2) use the private key in SSL handshake
 * 		3) delete private key (not the sealed data)
 * Each child process has a SSCB 2 to handle the connection with a client
 * Each child process has to register SSCB 2
 *
 * ********************************************************************************/

/* This file is the source of SSCB 2
 * written by Zongwei Zhou on Feb 17, 2010 */


#include  <openssl/sscb2.h>
#include  "rsa.h"
#include  "puttymem.h"
/* Intel VMX, commenting this would enable AMD SVM */
#define  IS_VMX

extern int sdatajunk2[5112] __attribute__ ((section (".sdata"))) = {2,3,4,5,6};
int paramjunk2[] __attribute__ ((section (".sparam"))) = {3,4,5,6,7};
int stackjunk2[] __attribute__ ((section (".sstack"))) = {4,5,6,7,8};

#ifndef IS_VMX
__attribute__ ((section (".sentry2") optimize("O0"))) int scode_unseal(unsigned int inaddr, unsigned int inlen,
                 unsigned int outaddr, unsigned int outlen_addr)
{
#if 1
  int ret;
  unsigned int inbuf[2]={inaddr, inlen};
  unsigned int outbuf[2]={outaddr, outlen_addr};
  __asm__ __volatile__(
                        "vmmcall\n\t"
			:"=a"(ret)
			: "a"(4), "c"((unsigned int)inbuf), "d"((unsigned int )outbuf));
  return 0;
#endif
#if 0
  int ret;
  unsigned int inbuf[2]={inaddr, inlen};
  unsigned int outbuf[2]={outaddr, outlen_addr};
  __asm__ __volatile__ ( 
		  "sub $0x20, %esp\n\t"
		  "mov 0x8(%ebp), %eax\n\t"
		  "mov %eax, (%esp)\n\t"
		  "mov 0xc(%ebp), %eax\n\t"
		  "mov %eax, 0x4(%esp)\n\t"
		  "lea (%esp), %eax\n\t"
		  "mov %eax, %ecx\n\t"
		  "mov 0x10(%ebp), %eax\n\t"
		  "mov %eax, 0x8(%esp)\n\t"
		  "mov 0x14(%ebp), %eax\n\t"
		  "mov %eax, 0xc(%esp)\n\t"
		  "lea 0x8(%esp), %eax\n\t"
		  "mov %eax, %edx\n\t"
		  "mov $0x4, %eax\n\t"
		  "vmmcall\n\t"
		  "add $0x20, %esp\n\t"
		  );
	return 0;
#endif
}
#else
__attribute__ ((section (".sentry2") optimize("O0"))) int scode_unseal(unsigned int inaddr, unsigned int inlen,
                 unsigned int outaddr, unsigned int outlen_addr)
{

#if 1
  int ret;
  unsigned int inbuf[2]={inaddr, inlen};
  unsigned int outbuf[2]={outaddr, outlen_addr};

  __asm__ __volatile__(
                        "vmcall\n\t"
			:"=a"(ret)
			: "a"(4), "c"((unsigned int)inbuf), "d"((unsigned int)outbuf));
	return 0;
#endif
#if 0
	int ret;
  unsigned int inbuf[2]={inaddr, inlen};
  unsigned int outbuf[2]={outaddr, outlen_addr};
 __asm__ __volatile__ ( 
		  "sub $0x20, %esp\n\t"
		  "mov 0x8(%ebp), %eax\n\t"
		  "mov %eax, (%esp)\n\t"
		  "mov 0xc(%ebp), %eax\n\t"
		  "mov %eax, 0x4(%esp)\n\t"
		  "lea (%esp), %eax\n\t"
		  "mov %eax, %ecx\n\t"
		  "mov 0x10(%ebp), %eax\n\t"
		  "mov %eax, 0x8(%esp)\n\t"
		  "mov 0x14(%ebp), %eax\n\t"
		  "mov %eax, 0xc(%esp)\n\t"
		  "lea 0x8(%esp), %eax\n\t"
		  "mov %eax, %edx\n\t"
		  "mov $0x4, %eax\n\t"
		  "vmcall\n\t"
		  "add $0x20, %esp\n\t"
		  );
	return 0;
#endif
}
#endif
__attribute__ ((section(".sentry"))) int sscb2 (unsigned char * pSealedData, int nSealedDataLen, 
		unsigned char * output, int * outputLen)
{
	scode_unseal((unsigned int)pSealedData, nSealedDataLen, (unsigned int)output, (unsigned int)(&outputLen));
}

int sscb (unsigned char * pPrivKey, int pPrivKeyLen, 
		unsigned char * input, int inputLen, unsigned char * output, int * outputLen)
{
	rsa_context * key;
	unsigned char * tmp;

	/* init rsa_context */
	mem_init();
	key = (rsa_context *) smalloc (sizeof(rsa_context));
	rsa_init(key, 0, 0);

	/* transform binary format to rsa private key */
	tmp = pPrivKey;
	if (bn2b(&tmp, &(key->N))) 	goto clean;
	if (bn2b(&tmp, &(key->E))) 	goto clean; 
	if (bn2b(&tmp, &(key->D)))  goto clean;
	if (bn2b(&tmp, &(key->P)))  goto clean;
	if (bn2b(&tmp, &(key->Q)))  goto clean;
	if (bn2b(&tmp, &(key->DP))) goto clean;
	if (bn2b(&tmp, &(key->DQ))) goto clean;
	if (bn2b(&tmp, &(key->QP))) goto clean;
	key->len=rsa_size(key);

	/* check input length and sign the input */
	if (inputLen != 36 || ((*outputLen = rsa_private_encrypt(inputLen, input, output, key, 0)) == -1))
		goto clean;
	
	/* clean and exit successfully */
	rsa_free(key);
	return 0;

clean:
	rsa_free(key);
	return 1;
}

__attribute__ ((section (".sentry2"))) int get_entry_dynamic_addr()
{
	int addr=0;
	addr++;
	return addr;
}

