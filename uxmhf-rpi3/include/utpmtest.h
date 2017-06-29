/*
	micro-tpm test application

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __UTPMTEST_H__
#define __UTPMTEST_H__

#define UAPP_UTPM_FUNCTION_INIT_MASTER_ENTROPY	0x10
#define UAPP_UTPM_FUNCTION_INIT_INSTANCE			0x11


#ifndef __ASSEMBLY__

typedef struct {
	uint8_t g_aeskey[TPM_AES_KEY_LEN_BYTES];
	uint8_t g_hmackey[TPM_HMAC_KEY_LEN];
	uint8_t g_rsakey[4]; //TODO: fix this to RSA key len when implemented
	TPM_RESULT result;
}utpm_init_master_entropy_param_t;


typedef struct {
	utpm_master_state_t utpm;
}utpm_init_instance_param_t;


#endif // __ASSEMBLY__



#endif //__UTPMTEST_H__
