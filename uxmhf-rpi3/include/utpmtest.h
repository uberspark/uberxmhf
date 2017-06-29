/*
	micro-tpm test application

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __UTPMTEST_H__
#define __UTPMTEST_H__

#define UAPP_UTPM_FUNCTION_INIT_MASTER_ENTROPY	0x10
#define UAPP_UTPM_FUNCTION_INIT_INSTANCE			0x11
#define UAPP_UTPM_FUNCTION_PCRREAD				0x12
#define UAPP_UTPM_FUNCTION_SEAL					0x13


#ifndef __ASSEMBLY__

typedef struct {
	uint8_t g_aeskey[TPM_AES_KEY_LEN_BYTES];
	uint8_t g_hmackey[TPM_HMAC_KEY_LEN];
	uint8_t g_rsakey[4]; //TODO: fix this to RSA key len when implemented

	utpm_master_state_t utpm;

	TPM_DIGEST pcr0;
	uint32_t pcr_num;

	TPM_PCR_INFO tpmPcrInfo;
	char seal_inbuf[16];
	uint32_t seal_inbuf_len;
	char seal_outbuf[32];
	uint32_t seal_outbuf_len;


	TPM_RESULT result;
} utpmtest_param_t;



#endif // __ASSEMBLY__



#endif //__UTPMTEST_H__
