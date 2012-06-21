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

/*
 * pehashdump.c
 * 
 * dump full and partial code-page hashes for a given PE section
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
 
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

#include "sha1.h"
#include "tomcrypt_custom.h"
#include "tomcrypt.h"

#define PAGE_SIZE_4K (1UL << 12)
#define PAGE_ALIGN_4K(size)	((size) & ~(PAGE_SIZE_4K - 1))

#define	__OUTPUT_HASHONLY__	1

#ifndef __OUTPUT_HASHONLY__

void sha1_section_print(char *filename, char *section_name, unsigned long int pagenum, unsigned long int pagebase,
	unsigned long int pageoffset, unsigned long int size, unsigned char *sha1sum, int partial){
	int i;

	if(size != PAGE_SIZE_4K && !partial)
		return;
		
	if(size == PAGE_SIZE_4K && partial)
		return;
		
	printf("{");
	printf("\"%s!%s!page(%u)\", 0x%08x, 0x%08x, 0x%08x, 0x%08x, ", filename, section_name, pagenum,
		pagenum, pagebase, pageoffset, size);
		
  printf("{");
  for (i = 0; i < 20; i ++){
        if (i < 19)
            printf("0x%02x, ", sha1sum[i]);
        else 
            printf("0x%02x", sha1sum[i]);
  }
  printf("}");
	printf("},\r\n");
}

#else

void sha1_section_print(char *filename, char *section_name, unsigned long int pagenum, unsigned long int pagebase,
	unsigned long int pageoffset, unsigned long int size, unsigned char *sha1sum, int partial){
	int i;

	if(size != PAGE_SIZE_4K && !partial)
		return;
		
	if(size == PAGE_SIZE_4K && partial)
		return;

  printf("%08x:%08x:", pageoffset, size);
		
  for (i = 0; i < 20; i ++){
	printf("%02x", sha1sum[i]);
  }
  printf("\r\n");
}



#endif //__OUTPUT_HASHONLY__


int sha1_section(char *filename, char *section_name, unsigned long int section_vma, unsigned long int section_size,
	unsigned long int section_fileoffset, int partial){
	FILE *fp;
	unsigned long int paligned_section_vma;
	unsigned long int i_pagebase, i_pageoffset, i_pagenum;
	long int i_size, i_fileoffset, i_size2;
	unsigned char *shabuf;
  unsigned char sha1sum[20];
  int ret;
//  sha1_context ctx;
  int rv=0;
  hash_state hs;
  

	
	fp=fopen(filename, "rb");
	if(!fp){
		printf("\nunable to open file: %s", filename);
		return 0;
	}

	paligned_section_vma=PAGE_ALIGN_4K(section_vma);
	//printf("\npaligned_section_vma=0x%08x", paligned_section_vma);
	
	shabuf=malloc(section_size);
	if(!shabuf){
		printf("\ncould not allocate memory of %u bytes", section_size);
		return 0;
	}

#ifndef __OUTPUT_HASHONLY__
	printf("/* filename=%s, section_name=%s */\r\n", filename, section_name);
#endif //__OUTPUT_HASHONLY__
	
	i_pagenum=0;
	i_pagebase=section_vma;
	i_pageoffset=(section_vma - paligned_section_vma);
	i_size = (long int)section_size;
	i_fileoffset=(long int)section_fileoffset;
	
	do{
		fseek(fp, i_fileoffset, SEEK_SET);
		i_size2= PAGE_SIZE_4K - i_pageoffset;
		if(i_size2 > i_size)
			i_size2=i_size;
		
		//read the buffer
		ret = fread(shabuf, i_size2, 1, fp);
    if (ret <= 0){
        //printf("\nunable to read %u bytes from file %s", i_size2, filename);        
        return 0;
    }
  
    //sha1_starts(&ctx);
    //sha1_update(&ctx, shabuf, i_size2);
    //sha1_finish(&ctx, sha1sum);
    rv = sha1_init( &hs);
    rv = sha1_process( &hs, shabuf, i_size2);
    rv = sha1_done( &hs, sha1sum);

		
		sha1_section_print(filename,
		section_name,
		i_pagenum,
			i_pagebase,
			(0 ? (i_size2 == PAGE_SIZE_4K) : i_pageoffset),
			i_size2,
			sha1sum,
			partial 
			);

		i_pagebase+=PAGE_SIZE_4K;
		i_fileoffset+=PAGE_SIZE_4K;
		i_pageoffset=0;
		i_pagenum++;		
		i_size-=(long)PAGE_SIZE_4K;
	}while(i_size > 0);
	
	return 1;
}

/*
 * main routine
 */
int main(int argc, char **argv)
{
    int i;
	
		//sha1 file section_vma section_size section_fileoffset
		if( argc != 7){
			printf("usage: sha1 file section_name section_vma section_size section_fileoffset partial\n");
			printf("note: all numbers are expected in hex");
			return 0;
		}
	
		i=sha1_section(argv[1], argv[2], strtoul(argv[3], NULL, 16), strtoul(argv[4], NULL, 16), strtoul(argv[5], NULL, 16),
			atoi(argv[6]));
    return i;
}
