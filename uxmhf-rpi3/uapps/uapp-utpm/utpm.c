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

////// PCR read
/* software tpm pcr read */
TPM_RESULT utpm_pcrread(TPM_DIGEST* pcr_value /* output */,
                        utpm_master_state_t *utpm, uint32_t pcr_num) /* inputs */
{
    if(!pcr_value || !utpm) { return UTPM_ERR_BAD_PARAM; }
    if(pcr_num >= TPM_PCR_NUM)  { return UTPM_ERR_PCR_OUT_OF_RANGE; }

	memcpy(pcr_value->value, utpm->pcr_bank[pcr_num].value, TPM_PCR_SIZE);
	return UTPM_SUCCESS;
}



////// PCR extend
/* software tpm pcr extend */
TPM_RESULT utpm_extend(TPM_DIGEST *measurement, utpm_master_state_t *utpm, uint32_t pcr_num)
{
    unsigned long outlen;
    int rv;

    if(!measurement || !utpm) { return UTPM_ERR_BAD_PARAM; }
    if(pcr_num >= TPM_PCR_NUM) { return UTPM_ERR_PCR_OUT_OF_RANGE; }

    _XDPRINTF_("utpm_extend: extending PCR %d\n", pcr_num);

    //print_hex("utpm_extend: PCR before: ", utpm->pcr_bank[pcr_num].value, TPM_HASH_SIZE);
    //print_hex("utpm_extend: measurement: ", measurement->value, TPM_HASH_SIZE);

    /* pcr = H( pcr || measurement) */
    outlen = sizeof(utpm->pcr_bank[pcr_num].value);
    rv = sha1_memory_multi( utpm->pcr_bank[pcr_num].value, &outlen,
                       utpm->pcr_bank[pcr_num].value, TPM_HASH_SIZE,
                       measurement->value, TPM_HASH_SIZE,
                            NULL, NULL);
    if (rv) {
      //abort();
    	return UTPM_ERR;
    }

    //print_hex("utpm_extend: PCR after: ", utpm->pcr_bank[pcr_num].value, TPM_HASH_SIZE);

	return UTPM_SUCCESS;
}
