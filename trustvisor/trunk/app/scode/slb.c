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

int sdatajunk[] __attribute__ ((section (".sdata")))  = {2,3,4,5,6};
int paramjunk[] __attribute__ ((section (".sparam"))) = {3,4,5,6,7};
int stackjunk[] __attribute__ ((section (".sstack"))) = {4,5,6,7,8};

enum VisorScmd
{
	VISOR_SCMD_REG = 1,
	VISOR_SCMD_UNREG = 2,
};

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

	int ssp;

	unsigned int addrdata;
	int num;
	int numPage;
	int textPage;

	/* parameter marshalling */
	params_info.params_num = 0;
	params_info.pm_str[0].type = PARAMS_TYPE_POINTER;  /* pointer */
	params_info.pm_str[0].size = 0;
	params_info.pm_str[1].type = PARAMS_TYPE_INTEGRE;  /* integer */
	params_info.pm_str[1].size = 0;
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
	textPage += scode_info.ps_str[1].page_num;

	scode_info.ps_str[2].type = SECTION_TYPE_PARAM;  
	scode_info.ps_str[2].start_addr = entry+numPage*PAGE_SIZE; 
	scode_info.ps_str[2].page_num = 1;
	numPage += scode_info.ps_str[2].page_num;

	scode_info.ps_str[3].type = SECTION_TYPE_STACK; 
	scode_info.ps_str[3].start_addr = entry+numPage*PAGE_SIZE; 
	scode_info.ps_str[3].page_num = 1;
	numPage += scode_info.ps_str[3].page_num;
	psinfo = (unsigned int)&scode_info;

	/* REMEMBER to replace ssp with the stack point for PAL,
	 * ssp is the end of you .stack section (-0x10 for safe) */
	ssp = (scode_info.ps_str[3].start_addr)+PAGE_SIZE-0x10;

	/* REMEMBER to active pages before you register them */        
	for( num = 0 ; num < numPage ; num++ )  {
		/* read all pages */
		addrdata = *((unsigned int *)(entry+num*PAGE_SIZE+10));
		printf("addrdata = %d\n", addrdata);
		/* write non-text pages */
		if (num >= textPage)
			*((unsigned int *)(entry+num*PAGE_SIZE+10)) = addrdata;
	}

	/* register scode */
	scode_registration(psinfo, ssp, pminfo, (unsigned int)entry);

	return 0;
}

int unreg_pal(unsigned int addr)
{
	scode_unregistration(addr);
	return 0;
}

// function main
// register some sensitive code and data in libfoo.so and call bar()
int main(void)
{
	register_pal();
	bar();
	unreg_pal((unsigned int)bar);
} 
