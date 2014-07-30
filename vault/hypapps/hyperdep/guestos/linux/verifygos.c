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
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
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
#include <string.h>

#define HYPERDEP_ACTIVATEDEP			0xC0
#define HYPERDEP_DEACTIVATEDEP			0xC1
#define HYPERDEP_INITIALIZE				0xC2


#if defined(__X86VMX__)
	static unsigned long int do_hypercall(unsigned long int eax, unsigned long int ecx, unsigned long int edx){
	__asm__ __volatile__(
							 "vmcall\n\t"
							 :"=a"(eax)
							 : "a"(eax), "c"(ecx), "d"(edx)
						);
		return eax;
	}

#elif defined(__X86SVM__)

	static unsigned long int do_hypercall(unsigned long int eax, unsigned long int ecx, unsigned long int edx){
		__asm__ __volatile__(
							 "vmmcall\n\t"
							 :"=a"(eax)
							 : "a"(eax), "c"(ecx), "d"(edx)
							 );
	  return eax;
	}

#else

	#error MUST choose proper TARGET_CPU in Makefile (x86svm or x86vmx)

#endif

//our buffer
unsigned char mybuffer[4096] __attribute__(( section(".palign_data") )) __attribute__((aligned(4096)));


void main(void){
	printf("\nverify application starting...\n");
	
	printf("\nmybuffer at %x", (unsigned long)&mybuffer);
	printf("\nsetting mybuffer to pattern 0xAA...");
	memset((void *)&mybuffer, 0xAA, sizeof(mybuffer));
	printf("\nverifying mybuffer[0]==0xAA");
	if(mybuffer[0] != 0xAA){
		printf("\nerror in setting mybuffer pattern");
		exit(1);
	}
	
	printf("\ninitializing hyperdep hypapp...");
	do_hypercall(HYPERDEP_INITIALIZE, 0, 0);
	printf(" --> done");
	
	printf("\nactivating DEP...");
	do_hypercall(HYPERDEP_ACTIVATEDEP, (unsigned long int)&mybuffer, 0);
	printf(" --> done");

	printf("\nde-activating DEP...");
	do_hypercall(HYPERDEP_DEACTIVATEDEP, (unsigned long int)&mybuffer, 0);
	printf(" --> done");
	
	printf("\nhyperdep application done.");
	printf("\n");
}
