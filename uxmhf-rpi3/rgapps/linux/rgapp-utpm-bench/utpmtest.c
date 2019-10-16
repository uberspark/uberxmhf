/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*
 * micro-tpm test program (utpmtest)
 * author: amit vasudevan (amitvasudevan@acm.org)
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>

#include <uhcall.h>
#include <xmhfcrypto.h>
#include <utpm.h>
#include <utpmtest.h>

#include <sys/time.h>

#define _XDPRINTF_ 	printf

uint8_t g_aeskey[TPM_AES_KEY_LEN_BYTES] =
		{
				0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
				0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18
		};

uint8_t g_hmackey[TPM_HMAC_KEY_LEN] =
		{
				0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x01, 0x02,
				0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x11, 0x12,
				0xaa, 0xbb, 0xcc, 0xdd
		};

uint8_t g_rsakey[] = {0x00, 0x00, 0x00, 0x00};

uint8_t digest[] =
		{ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01
		};


char *seal_inbuf = "0123456789abcde";



__attribute__((aligned(4096))) __attribute__((section(".data"))) utpmtest_param_t utpmtest_param;


void utpm_setup(uint32_t cpuid) {
	//sanity check
	if( sizeof(utpmtest_param_t) > 4096){
		exit(1);
	}

	utpmtest_param.magic = 0xDEADBEEF;

	memcpy(&utpmtest_param.g_aeskey, &g_aeskey, TPM_AES_KEY_LEN_BYTES);
	memcpy(&utpmtest_param.g_hmackey, &g_hmackey, TPM_HMAC_KEY_LEN);
	memcpy(&utpmtest_param.g_rsakey, &g_rsakey, 4); //TODO: change to RSA key len when implemented

	if(!uhcall(UAPP_UTPM_FUNCTION_INIT_MASTER_ENTROPY, &utpmtest_param, sizeof(utpmtest_param_t))){
		exit(1);
	}

	if (utpmtest_param.result != UTPM_SUCCESS){
		exit(1);
	}
}
	
//////
// utpm test
//////
void utpm_test(uint32_t cpuid)
{
	//sanity check
	if( sizeof(utpmtest_param_t) > 4096){
		exit(1);
	}

	if(!uhcall(UAPP_UTPM_FUNCTION_INIT_INSTANCE, &utpmtest_param, sizeof(utpmtest_param_t))){
		exit(1);
	}

	utpmtest_param.pcr_num=0;
	if(!uhcall(UAPP_UTPM_FUNCTION_PCRREAD, &utpmtest_param, sizeof(utpmtest_param_t))){
		exit(1);
	}
	if (utpmtest_param.result != UTPM_SUCCESS){
		exit(1);
	}


	memcpy(&utpmtest_param.measurement.value, &digest, sizeof(digest));
	utpmtest_param.pcr_num = 0;

	if(!uhcall(UAPP_UTPM_FUNCTION_EXTEND, &utpmtest_param, sizeof(utpmtest_param_t))){
		exit(1);
	}
	if (utpmtest_param.result != UTPM_SUCCESS){
		exit(1);
	}


	utpmtest_param.pcr_num=0;
	if(!uhcall(UAPP_UTPM_FUNCTION_PCRREAD, &utpmtest_param, sizeof(utpmtest_param_t))){
		exit(1);
	}
	if (utpmtest_param.result != UTPM_SUCCESS){
		exit(1);
	}

}



int main(){

  struct timeval tv1, tv2;
   printf("Starting usr mode utpm test...\n");
   utpm_setup(0);   
   gettimeofday(&tv1, NULL);
   utpm_test(0);
   gettimeofday(&tv2, NULL);
   printf("End of utpm test\n");
   printf("Total time = %f seconds\n", (double) (tv2.tv_usec-tv1.tv_usec)/1000000 + (double) (tv2.tv_sec - tv1.tv_sec));
   return 0;
}
