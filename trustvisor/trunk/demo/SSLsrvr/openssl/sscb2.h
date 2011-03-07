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

#define  MAX_PARAMS_NUM 10
#define PARAMS_TYPE_INTEGRE 1
#define PARAMS_TYPE_POINTER 2

#define  SECTION_TYPE_SCODE 1
#define  SECTION_TYPE_SDATA 2
#define  SECTION_TYPE_PARAM 3
#define  SECTION_TYPE_STACK 4
#define  SECTION_TYPE_STEXT 5
/* definde for scode sections info */
#define MAX_SECTION_NUM 10  /* max sections that are allowed in scode registration */
#define PAGE_SIZE 0x1000

struct scode_params_struct{
    int type;  /* 1: integer ;  2:pointer*/
    int size;
};

struct scode_params_info{
   int params_num;
   struct scode_params_struct pm_str[MAX_PARAMS_NUM];
};

struct scode_sections_struct{
    int type;  
	unsigned int start_addr;
    int page_num;
};

struct scode_sections_info{
   int section_num;
   struct scode_sections_struct ps_str[MAX_SECTION_NUM];
};


int sdatajunk2[5112];
int sscb2 (unsigned char * pSealedData, int nSealedDataLen, 
		unsigned char * output, int * outputLen);
int sscb (unsigned char * pPrivKey, int pPrivKeyLen, unsigned char * input, int inputLen, unsigned char * output, int * outputLen);
int get_entry_dynamic_addr();
