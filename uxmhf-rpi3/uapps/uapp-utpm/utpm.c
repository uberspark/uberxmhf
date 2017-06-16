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

