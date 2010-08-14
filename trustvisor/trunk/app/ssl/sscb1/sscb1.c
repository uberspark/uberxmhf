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


/* This file is the source of SSCB 1
 * written by Zongwei Zhou on Feb 17, 2010 */

#include  "sscb1.h"
#include  "magic_addr.h"
#include  <stdio.h>
#include  <sys/mman.h>

int sdatajunk[] __attribute__ ((section (".sdata"))) = {2,3,4,5,6};
int paramjunk[] __attribute__ ((section (".sparam"))) = {3,4,5,6,7};
int stackjunk[] __attribute__ ((section (".sstack"))) = {4,5,6,7,8};

int scode_registration(unsigned int pageinfo, unsigned int ssp, unsigned int params, unsigned int entry)
{
	int ret;
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(1), "b"(pageinfo), "d"(ssp), "S"(params), "D"(entry));
}

int scode_unregistration(unsigned int start)
{
	int ret;
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(2), "b"(start));
}

__attribute__ ((section(".sentry"))) int sscb1 (unsigned char * pSealedData, int * pSealedDataLen, 
		unsigned char * pCertReq, int * pCertReqLen,
		unsigned char * pPrivKey, int nPrivKeyLen)
{
	/* this value should be the hash value of SSCB 2 */
	unsigned char sscb2_hash[] = {0x21, 0x3c, 0x24, 0x40, 0x44, 0x4a, 0x63, 0xf5, 0x11, 0xec,
                                  0xec, 0x89, 0x14, 0x49, 0xb, 0x2b, 0x1e, 0x39, 0xa ,0x30};

	/* seal the private key for SSCB 2, output sealed data */
	scode_seal((unsigned int)sscb2_hash, (unsigned int)pPrivKey, nPrivKeyLen, (unsigned int)pSealedData, (unsigned int)pSealedDataLen);


	/* for test, no certReq output */
	pCertReq++;
	pCertReq--;
	*pCertReqLen = 0;

	return 0;
}

__attribute__ ((section(".stext"))) int scode_seal(unsigned int pcrAtRelease_addr,
               unsigned int inaddr, unsigned int inlen,
               unsigned int outaddr, unsigned int outlen_addr)
{
  int ret;
  __asm__ __volatile__(
                        "vmmcall\n\t"
			:"=a"(ret)
			: "a"(13), "b"(inaddr), "c"(inlen), "d"(pcrAtRelease_addr), "S"(outaddr), "D"(outlen_addr));
}

int register_sscb2()
{

	unsigned int i_saddr; 
	struct scode_params_info params_info;
	struct scode_sections_info scode_info;

	unsigned int i_pminfo; 
	unsigned int i_psinfo; 
	int ssp;

	unsigned int addrdata;
	int num;
	int numPage;
	int textPage;

	/* parameter marshalling */
	params_info.params_num = 4;
	params_info.pm_str[0].type = PARAMS_TYPE_POINTER; 
	params_info.pm_str[0].size = 170;
	params_info.pm_str[1].type = PARAMS_TYPE_INTEGRE; 
	params_info.pm_str[1].size = 1;
	params_info.pm_str[2].type = PARAMS_TYPE_POINTER; 
	params_info.pm_str[2].size = 170;
	params_info.pm_str[3].type = PARAMS_TYPE_POINTER; 
	params_info.pm_str[3].size = 1;

	i_pminfo = (unsigned int)&params_info;

	/* get the start address and number of page in sensitive code block */
	i_saddr = get_addr();
	i_saddr = (unsigned int)(((*((int *)MAGIC_ADDR))>>12)<<12);
	/* SENTRY+STEXT -- 5 pages
	 * SDATA	-- 5 pages
	 * SPARAM 	-- 1 pages
	 * SSTACK 	-- 1 pages 
	 * TRUNK_PAGE   -- 1 pages
	 */
	numPage=12;
	textPage=5;

	/* scode section info */
	scode_info.section_num = 6;
	scode_info.ps_str[0].type = SECTION_TYPE_SCODE; 
	scode_info.ps_str[0].start_addr = i_saddr; 
	scode_info.ps_str[0].page_num = 1;

	scode_info.ps_str[1].type = SECTION_TYPE_STEXT; 
	scode_info.ps_str[1].start_addr = i_saddr+PAGE_SIZE; 
	scode_info.ps_str[1].page_num = 4;

	scode_info.ps_str[2].type = SECTION_TYPE_SDATA;  
	scode_info.ps_str[2].start_addr = i_saddr+5*PAGE_SIZE; 
	scode_info.ps_str[2].page_num = 5;

	scode_info.ps_str[3].type = SECTION_TYPE_PARAM;  
	scode_info.ps_str[3].start_addr = i_saddr+10*PAGE_SIZE; 
	scode_info.ps_str[3].page_num = 1;

	scode_info.ps_str[4].type = SECTION_TYPE_STACK; 
	scode_info.ps_str[4].start_addr = i_saddr+11*PAGE_SIZE; 
	scode_info.ps_str[4].page_num = 1;

	/* page for get_pc_thunk.*, shared between SSCB and regular code */
	scode_info.ps_str[5].type = SECTION_TYPE_STEXT; 
	scode_info.ps_str[5].start_addr = ((i_saddr-ENTRY_ADDR+THUNK_ADDR)>>12)<<12; 
	scode_info.ps_str[5].page_num = 1;

	i_psinfo = (unsigned int)&scode_info;

	/* set memory protection of SSCB read-only pages to R/W
         * so that we can use Copy on Write to replicate these pages
         * before registration
         */
	if (mprotect((void *)i_saddr,(size_t)((numPage-2)*PAGE_SIZE), PROT_READ|PROT_WRITE)!=0) {
		printf("set text page to rw error!\n");
		return 1;
	}
	if (mprotect((void *)(scode_info.ps_str[5].start_addr),(size_t)PAGE_SIZE, PROT_READ|PROT_WRITE ) !=0) {
		printf("set thunk page to rw error!\n");
		return 1;
	}

	/* REMEMBER to active pages before you register them */        
	for( num = 0 ; num<numPage ; num++ )  {
		// read all pages
		addrdata = *((unsigned int *)(i_saddr+num*PAGE_SIZE+10));
		printf("addrdata = %d\n", addrdata);
		/* copy on write */
		*((unsigned int *)(i_saddr+num*PAGE_SIZE+10)) = addrdata;
	}
	addrdata = *((unsigned int *)(scode_info.ps_str[5].start_addr));
	printf("addrdata = %d\n", addrdata);
	*((unsigned int *)(scode_info.ps_str[5].start_addr)) = addrdata;

	/* set the text pages to read-only and executable */
	if (mprotect((void *)i_saddr,(size_t)(textPage*PAGE_SIZE), PROT_READ|PROT_EXEC)!=0) {
		printf("set text page to r error!\n");
		return 1;
	}
	if (mprotect((void *)(scode_info.ps_str[5].start_addr),(size_t)PAGE_SIZE, PROT_READ|PROT_EXEC)!=0) {
		printf("set thunk page to r error!\n");
		return 1;
	}

	/* register scode */
	/* Remember to replace ssp with the stack point for sensitive code,
	 * ssp should be at the end of you .stack section (-0x10 for safe) */
	ssp = (scode_info.ps_str[4].start_addr)+PAGE_SIZE-0x10;
	scode_registration(i_psinfo, ssp, i_pminfo, (unsigned int)i_saddr);
	return 0;
}


int register_sscb1(int len)
{

	unsigned int i_saddr; 
	struct scode_params_info params_info;
	struct scode_sections_info scode_info;

	unsigned int i_pminfo; 
	unsigned int i_psinfo; 
	int ssp;

	unsigned int addrdata;
	int num;
	int numPage;

	/* parameter marshalling */
	params_info.params_num = 6;
	params_info.pm_str[0].type = PARAMS_TYPE_POINTER; 
	params_info.pm_str[0].size = 170;
	params_info.pm_str[1].type = PARAMS_TYPE_POINTER; 
	params_info.pm_str[1].size = 1;
	params_info.pm_str[2].type = PARAMS_TYPE_POINTER; 
	params_info.pm_str[2].size = 4;
	params_info.pm_str[3].type = PARAMS_TYPE_POINTER; 
	params_info.pm_str[3].size = 1;
	params_info.pm_str[4].type = PARAMS_TYPE_POINTER; 
	params_info.pm_str[4].size = len/4+1;
	params_info.pm_str[5].type = PARAMS_TYPE_INTEGRE; 
	params_info.pm_str[5].size = 1;

	i_pminfo = (unsigned int)&params_info;

	/* get the start address and number of page in sensitive code block */
	i_saddr = (int)sscb1;
	numPage=5;

	/* scode section info */
	scode_info.section_num = 4;
	scode_info.ps_str[0].type = SECTION_TYPE_SCODE; 
	scode_info.ps_str[0].start_addr = i_saddr; 
	scode_info.ps_str[0].page_num = 2;

	scode_info.ps_str[1].type = SECTION_TYPE_SDATA;  
	scode_info.ps_str[1].start_addr = i_saddr+2*PAGE_SIZE; 
	scode_info.ps_str[1].page_num = 1;

	scode_info.ps_str[2].type = SECTION_TYPE_PARAM; 
	scode_info.ps_str[2].start_addr = i_saddr+3*PAGE_SIZE; 
	scode_info.ps_str[2].page_num = 1;
		
	scode_info.ps_str[3].type = SECTION_TYPE_STACK; 
	scode_info.ps_str[3].start_addr = i_saddr+4*PAGE_SIZE; 
	scode_info.ps_str[3].page_num = 1;

	/* REMEMBER to active pages before you register them */        
	for( num = 0 ; num<numPage ; num++ )  {
		// read all pages
		addrdata = *((unsigned int *)(i_saddr+num*PAGE_SIZE+10));
		printf("addrdata = %d!\n", addrdata);
		// copy on write 
		if (num >=2 ) {
		    *(unsigned int *)(i_saddr+num*PAGE_SIZE+10) = addrdata;
        	}
	}
	i_psinfo = (unsigned int)&scode_info;

	/* register scode */
	/* Remember to replace ssp with the stack point for sensitive code,
	 * ssp should be at the end of you .stack section (-0x10 for safe) */
	ssp = (scode_info.ps_str[3].start_addr)+PAGE_SIZE-0x10;
	scode_registration(i_psinfo, ssp, i_pminfo, (unsigned int)i_saddr);
	return 0;
}

int unreg_sscb(unsigned int addr)
{
	scode_unregistration(addr);
	return 0;
}

