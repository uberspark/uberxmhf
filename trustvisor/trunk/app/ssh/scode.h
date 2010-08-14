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
#include <termios.h>
#include <unistd.h>
#define TPM_PCR_SIZE 20
#define TPM_RSA_KEY_SIZE 128
#define TPM_AES_KEY_SIZE 128
#define SEAL_DATA_SIZE 256
#define TPM_HASH_SIZE 20
#define TPM_NONCE_SIZE 20
#define PAGE_SIZE 0x1000
#define PASSWORD_SIZE 12

enum VisorScmd
{
  VISOR_SCMD_REG = 1,
  VISOR_SCMD_UNREG = 2,
  VISOR_STPM_PCRREAD = 11,
  VISOR_STPM_EXTEND = 12,
  VISOR_STPM_SEAL = 13,
  VISOR_STPM_UNSEAL = 14,
  VISOR_STPM_QUOTE = 15,
};

/* define for attribute */
#ifndef FC
#define FC __attribute__((fastcall))
#define RP3 __attribute__((regparm(3)))
#endif

/* definde for parameter marshalling */

#define MAX_PARAMS_NUM 5
#define PARAMS_TYPE_INTEGER 1
#define PARAMS_TYPE_POINTER 2

struct scode_params_struct{
    int type;  /* 1: integer ;  2:pointer*/
    int size;
};

struct scode_params_info{
   int params_num;
   struct scode_params_struct pm_str[MAX_PARAMS_NUM];
};

/*  test function */
//int readpass(void);
int ssub(int value) FC;
int sadd2(int a, int b) RP3;
int sadd3(int a, int b, int c) RP3;
int sadd4(int a, int b, int c, int d) RP3;
int sadd(int value);
int sadd5(unsigned char* value, int len); //RP3;
int shash(unsigned char* input, int inlen, unsigned char* out);
int scode_pcrread(unsigned int addr);
int scode_pcrextend(unsigned int addr, unsigned int len);
int scode_seal(unsigned int pcrAtRelease_addr,
               unsigned int inaddr, unsigned int inlen,
			   unsigned int outaddr, unsigned int outlen_addr);
int scode_unseal(unsigned int inaddr, unsigned int inlen,
                 unsigned int outaddr, unsigned int outlen_addr);
int scode_quote(unsigned int nonce_addr, unsigned int outaddr, unsigned int outlen_addr);

/* scode for ssh */
int scode_sshserver(unsigned int cipher_addr, unsigned int sealdata_addr, 
                    unsigned int nonce_addr, unsigned int hash_addr, unsigned int mode);



