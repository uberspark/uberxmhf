/*
 * utpm interface
 * adapted from trustvisor utpm by amit vasudevan (amitvasudevan@acm.org
 */

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>
#include <utpm.h>

//////
// global data variables
//////
// keys for software TPM seal, unseal and quote operations
__attribute__((section(".data"))) uint8_t g_aeskey[TPM_AES_KEY_LEN_BYTES];
__attribute__((section(".data"))) uint8_t g_hmackey[TPM_HMAC_KEY_LEN];
//rsa_key g_rsa_key;



//////
// interface functions
//////


////// initialize master entropy
/**
 * This function is expected to only be called once during the life of
 * anything that uses this uTPM implementation.  This function will
 * need significant modification if we ever decide to support
 * arbitrarily many signing keys for uTPM instances.
 */
TPM_RESULT utpm_init_master_entropy(uint8_t *aeskey,
                                    uint8_t *hmackey,
                                    void /*rsa_context*/ *rsa) {
    if(!aeskey || !hmackey || !rsa) {
        return UTPM_ERR_INSUFFICIENT_ENTROPY;

    }

    memcpy(g_aeskey, aeskey, TPM_AES_KEY_LEN_BYTES);
    memcpy(g_hmackey, hmackey, TPM_HMAC_KEY_LEN);
    //memcpy(&g_rsa_key, rsa, sizeof(g_rsa_key));

    /* ensure libtomcrypto's math descriptor is initialized */
    //if (!ltc_mp.name) {
    //  ltc_mp = ltm_desc;
    //}

    return UTPM_SUCCESS;
}


////// initialize instance
void utpm_init_instance(utpm_master_state_t *utpm) {
    if(NULL == utpm) return;

    memset(utpm->pcr_bank, 0, TPM_PCR_SIZE*TPM_PCR_NUM);

}



