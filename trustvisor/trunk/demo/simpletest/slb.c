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

#include <stdio.h>
#include <stdlib.h>
#include "scode.h"
#include "foo.h"
//#include  "config.h"
#ifndef IS_WINDOWS
#include  <sys/mman.h>
#include  <errno.h>
#include  <string.h>
#endif

int sdatajunk[] __attribute__ ((section (".sdata")))  = {2,3,4,5,6};
int paramjunk[] __attribute__ ((section (".sparam"))) = {3,4,5,6,7};
int stackjunk[] __attribute__ ((section (".sstack"))) = {4,5,6,7,8};

#ifndef TEST_WITHOUTPARAM
#define  INPUT1_STR_SIZE_BYTE 640
#define  INPUT1_STR_SIZE_INT 160
char input[INPUT1_STR_SIZE_BYTE]="";

#define  INPUT2_STR_SIZE_BYTE 4 
#define  INPUT2_STR_SIZE_INT 1
int len=0;

int flag=1;
#endif

#ifndef TEST_VMMCALL
/* Routines for preparing input and registering PAL 
 *
 * called by untrusted application, not in PAL
 * */
int register_pal()
{
	unsigned int entry; 
	struct scode_params_info params_info;
	struct scode_sections_info scode_info;

	unsigned int pminfo; 
	unsigned int psinfo; 

	unsigned int addrdata;
	int num;
	int numPage;
	int textPage;

	/* parameter marshalling 
	 * * size always denotes how many integers are there
	 * for PARAMS_TYPE_INTEGER, size = 1
	 * for PARAMS_TYPE_POINTER, size = ceiling(string_size/4) */
#ifdef TEST_WITHOUTPARAM
	params_info.params_num = 0;
	params_info.pm_str[0].type = PARAMS_TYPE_POINTER;  /* pointer */
	params_info.pm_str[0].size = 0;
	params_info.pm_str[1].type = PARAMS_TYPE_INTEGER;  /* integer */
	params_info.pm_str[1].size = 0;
#else
	params_info.params_num = 3;
	params_info.pm_str[0].type = PARAMS_TYPE_POINTER;  /* pointer */
	params_info.pm_str[0].size = INPUT1_STR_SIZE_INT;
	params_info.pm_str[1].type = PARAMS_TYPE_POINTER;  /* pointer */
	params_info.pm_str[1].size = INPUT2_STR_SIZE_INT;
	params_info.pm_str[2].type = PARAMS_TYPE_INTEGER;  /* integer */
	params_info.pm_str[2].size = 1;
#endif
	pminfo = (unsigned int)&params_info;

	/* scode page sections info */
	entry = (unsigned int)bar;

	scode_info.section_num = 4;
	numPage=0;
	textPage=0;

	scode_info.ps_str[0].type = SECTION_TYPE_SCODE; 
	scode_info.ps_str[0].start_addr = entry; 
	scode_info.ps_str[0].page_num = 1;
	numPage += scode_info.ps_str[0].page_num;
	textPage += scode_info.ps_str[0].page_num;

	scode_info.ps_str[1].type = SECTION_TYPE_SDATA; 
	scode_info.ps_str[1].start_addr = entry+numPage*PAGE_SIZE; 
	scode_info.ps_str[1].page_num = 1;
	numPage += scode_info.ps_str[1].page_num;

	scode_info.ps_str[2].type = SECTION_TYPE_PARAM;  
	scode_info.ps_str[2].start_addr = entry+numPage*PAGE_SIZE; 
	scode_info.ps_str[2].page_num = 1;
	numPage += scode_info.ps_str[2].page_num;

	scode_info.ps_str[3].type = SECTION_TYPE_STACK; 
	scode_info.ps_str[3].start_addr = entry+numPage*PAGE_SIZE; 
	scode_info.ps_str[3].page_num = 1;
	numPage += scode_info.ps_str[3].page_num;
	psinfo = (unsigned int)&scode_info;

	/* REMEMBER to active pages before you register them */        
	for( num = 0 ; num < numPage ; num++ )  {
		/* read all pages */
		addrdata = *((unsigned int *)(entry+num*PAGE_SIZE+10));
		//printf("addrdata = %d\n", addrdata);
		/* write non-text pages */
		if (num >= textPage) {
#ifndef IS_WINDOWS
			if (mprotect((void *)(entry+num*PAGE_SIZE),PAGE_SIZE, PROT_READ | PROT_WRITE)!=0) {
				printf("mprotect error %s!\n",strerror(errno));
				return 1;
			}
#endif
			*((unsigned int *)(entry+num*PAGE_SIZE+10)) = addrdata;
		}
	}

	/* register scode */
	scode_registration(psinfo, pminfo, (unsigned int)entry);

	return 0;
}

int unreg_pal(unsigned int addr)
{
	scode_unregistration(addr);
	return 0;
}
#endif
// function main
// register some sensitive code and data in libfoo.so and call bar()
int main(void)
{
#ifdef TEST_VMMCALL
	printf("start testing VMMCAL!\n");
	scode_test();
	printf("finish testing VMMCAL!\n");
#else

#ifdef TEST_QUOTE
	unsigned int * output;
	unsigned char * pdata;
	int num, i,j;
#endif

	printf("start registering PAL!\n");
	if (register_pal())
		return;
	printf("start runing PAL!\n");

#ifdef TEST_WITHOUTPARAM
	bar();
#endif

#ifdef TEST_PARAM
	printf("str[0] before PAL is %d!\n", input[0]);
	bar(input, (char *)(&len), flag);
	printf("str[0] after PAL is %d!\n", input[0]);
#endif

#ifdef TEST_SEAL
	printf("str[0] before PAL is %d!\n", input[0]);
	bar(input, (char *)(&len), flag);
	printf("str[0] after PAL is %d!\n", input[0]);
	if (input[0] != 0x0c) {
		printf("error!!!!!\n");
	} else {
		printf("no error!!!!!\n");
	}
#endif
#ifdef TEST_QUOTE
	printf("str[0] before PAL is %d!\n", input[0]);
	bar(input, (char *)(&len), flag);
	printf("str[0] after PAL is %d!\n", input[0]);
	printf("output len = %d!\n", len);
	output = (unsigned int *)input;
	if (output[0] != 0x00000101 || output[1] != 0x544f5551) {
		printf("quote header error!\n");
		return 1;
	}
	num = output[2];
	if (num > 4) {
		printf("quote pcr sel error!\n");
		return 1;
	}
	pdata = input+8+4+4*num;
	for( i=0 ; i<num ; i++ )  {
		printf("PCR[%d] = ", output[3+i]);
		for (j=0; j<20; j++) 
			printf("%#x ", *(pdata+i*20+j));
		printf("\n");
	}
	pdata = input+8+4+24*num;
	printf("nonce = ");
	for( i=0 ; i<20 ; i++ )  
		printf("%x ", *(pdata+i));
	printf("\n");
#endif

	printf("start unregistering PAL!\n");
	unreg_pal((unsigned int)bar);
	printf("Program finish!\n");

#endif
} 
