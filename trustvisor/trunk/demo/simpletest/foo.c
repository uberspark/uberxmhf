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

#include  "foo.h"
#include  "scode.h"
#define  NUM 10

#ifndef TEST_VMMCALL
/* sensitive code  */
#ifdef TEST_WITHOUTPARAM
__attribute__ ((section (".entry")))
void bar(void) 
{
	asm("nop"::);
	asm("nop"::);
	asm("nop"::);
	asm("nop"::);
}
#endif

#ifdef TEST_PARAM
__attribute__ ((section (".entry")))
void bar(char * str, char * len, int flag) 
{
	if (flag)
		str[0]=0x0f;
	else
		str[0]=0x0d;
}
#endif

#ifdef TEST_SEAL
__attribute__ ((section (".entry")))
void bar(char * str, char * len, int flag) 
{
	int i;
	unsigned char inputdata[16]="I am input data!";
	unsigned int inputlen = 16;
	unsigned char outputdata[100]="";
	unsigned int outputlen;
	unsigned char tmp [100]="";
	unsigned int tmplen;

	scode_seal(0,(unsigned int)inputdata,inputlen,(unsigned int)outputdata,(unsigned int)((unsigned int *)(&outputlen)));

	scode_unseal((unsigned int)outputdata, outputlen, (unsigned int)tmp, (unsigned int)((unsigned int *)(&tmplen)));

	if (tmplen != inputlen) {
		str[0]=0x0f;
		return;
	}

	for( i=0 ; i<tmplen ; i++ )  {
		if (tmp[i]!=inputdata[i]) {
			str[0]=0x0d;
			return;
		}
	}
	str[0]=0x0c;
}
#endif

#ifdef TEST_QUOTE
__attribute__ ((section (".entry")))
void bar(char * str, char * len, int flag) 
{
	int i;
	unsigned char nonce[20];
	unsigned char tpmsel[8];
	*((unsigned int *)tpmsel)=1;
	*((unsigned int *)(tpmsel+4))=0;

	for( i=0 ; i<20 ; i++ )  {
		nonce[i]=((char)i)+tpmsel[i%8];
	}

	scode_quote((unsigned int)nonce,(unsigned int)tpmsel,(unsigned int)str,(unsigned int)((unsigned int *)len));
}

#endif
#endif

int barbar(int b)
{
	int i;
	for( i=0 ; i<20 ; i++ )  {
		b+=i;
	}
	return b;
}

int foo(int b)
{
	do {
		b++;
	} while (b%20==0);
	b=foofoo(b);
	b=barbar(b);
	return b;
}

int foofoo(int a)
{
	a=a*a;
	a=a/4;
	a=a+123;
	return a;
}


