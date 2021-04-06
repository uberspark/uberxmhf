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
	micro-tpm test application

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __UTPMTEST_H__
#define __UTPMTEST_H__

#define UAPP_UTPM_FUNCTION_INIT_MASTER_ENTROPY	0x10
#define UAPP_UTPM_FUNCTION_INIT_INSTANCE			0x11
#define UAPP_UTPM_FUNCTION_PCRREAD				0x12
#define UAPP_UTPM_FUNCTION_EXTEND					0x13
#define UAPP_UTPM_FUNCTION_SEAL					0x14
#define UAPP_UTPM_FUNCTION_UNSEAL					0x15


#ifndef __ASSEMBLY__

typedef struct {
	uint32_t magic;
	uint8_t g_aeskey[TPM_AES_KEY_LEN_BYTES];
	uint8_t g_hmackey[TPM_HMAC_KEY_LEN];
	uint8_t g_rsakey[4]; //TODO: fix this to RSA key len when implemented

	utpm_master_state_t utpm;

	TPM_DIGEST pcr0;
	uint32_t pcr_num;

	TPM_DIGEST measurement;


	TPM_PCR_INFO tpmPcrInfo;
	char seal_inbuf[16];
	uint32_t seal_inbuf_len;
	char seal_outbuf[128];
	uint32_t seal_outbuf_len;

	char seal_outbuf2[128];
	uint32_t seal_outbuf2_len;
	TPM_COMPOSITE_HASH digestAtCreation;


	TPM_RESULT result;
} utpmtest_param_t;



#endif // __ASSEMBLY__



#endif //__UTPMTEST_H__
