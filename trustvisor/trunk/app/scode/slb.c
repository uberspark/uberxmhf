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
#include <foo.h>
#include "scode.h"
#include "foo.h"

#define PAGE_SIZE 0x1000

enum VisorScmd
{
	VISOR_SCMD_REG = 1,
	VISOR_SCMD_UNREG = 2,
};

//function scode_registration
//todo: register secure sensitive code
int scode_registration(unsigned int start, unsigned int size, unsigned int ssp, unsigned int params)
{
	int ret;
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(VISOR_SCMD_REG), "b"(start), "c"(size), "d"(ssp), "S"(params));
}

// function scode_unregistration
// todo: unregister secure sensitive code
int scode_unregistration(unsigned int start)
{
	int ret;
	__asm__ __volatile__(
			"vmmcall\n\t"
			:"=a"(ret)
			: "a"(VISOR_SCMD_UNREG), "b"(start));
}


// function main
// register some sensitive code and data in libfoo.so and call bar()
int main(void)
{
	unsigned int i_saddr; /*sensitive code begin address*/
	unsigned int i_pminfo; /* sensitive code parameter info address*/
	int ssp;
	//int data[10];
	unsigned int addrdata;
	int num;
	int numPage;

	/* parameter marshalling */
	/* now bar() don't have any input and output,
	 * so all zero :-) */
	struct scode_params_info params_info;
	params_info.params_num = 0;
	params_info.pm_str[0].type = PARAMS_TYPE_POINTER;  /* pointer */
	params_info.pm_str[0].size = 0;
	params_info.pm_str[1].type = PARAMS_TYPE_INTEGRE;  /* integer */
	params_info.pm_str[1].size = 0;
	i_pminfo = (unsigned int)&params_info;

	/* get the start address and number of page in sensitive code block */

	/* The content stored in 0x8049xxx is the actual address of bar(), 
	 * and also the start address of our sensitive code block.
	 * you need to do "objdump -D slb" and find the plt entry of bar()
	 * For example:
	 *     8040000 <bar@plt>
	 *     8040001 jmp *0x80497c0
	 * Get the address after "jmp *" and hardcode it below
	 * You also need to know how many pages are there in you scode block,
	 * (include scode, param, stac section in shared library libfoo.so)
	 * and change numPage below */
	//i_saddr = (unsigned int)*((int *)MAGIC_ADDR);
	i_saddr = (int)bar;
	numPage=3;
	printf("i_saddr = %x, num of pages is %d!\n", i_saddr, numPage);

	/* REMEMBER to active pages before you register them */        
	for( num = 0 ; num<numPage ; num++ )  {
		// read all pages
		addrdata = *(unsigned int *)(i_saddr+num*PAGE_SIZE);
		printf("addrdata = %x!\n",addrdata);
		if (num == numPage-1)
		    *(unsigned int *)(i_saddr+num*PAGE_SIZE) = addrdata+1;
		//data[num] = addrdata;
		// write (will create a copy - COW)
		//*(unsigned int *)(i_saddr) = addrdata;
	}
#if 0
	bar();
#endif

#if 1        
	/* register scode */

	/* Remember to replace ssp with the stack point for sensitive code,
	 * ssp should be at the end of you .stack section (-0x10 for safe) */
	ssp = (((unsigned int)i_saddr + numPage*PAGE_SIZE) & ~(PAGE_SIZE - 1)) - 0x10;
	printf("ssp is %x!\n", ssp);

	scode_registration((unsigned int)i_saddr, numPage*PAGE_SIZE, ssp, i_pminfo);
	printf("registration finished!\n");
#endif
#if 1
	bar();
#endif

#if 1
	// unregister scode 
	scode_unregistration((unsigned int)i_saddr);
#endif 
} 
