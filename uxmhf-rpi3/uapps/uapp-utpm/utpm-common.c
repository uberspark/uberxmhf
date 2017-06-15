/*
 * utpm common functions
 * adapted from trustvisor utpm by amit vasudevan (amitvasudevan@acm.org
 */

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>
#include <utpm.h>

void utpm_pcr_select_i(TPM_PCR_SELECTION *tpmsel, uint32_t i) {
    /* TODO: fail loudly if any of these conditions do not hold */
    if(NULL == tpmsel) return;
    if(i >= TPM_PCR_NUM) return;
    /*if(i/8 >= tpmsel->sizeOfSelect) return; */ /* deprecated in favor of
                                                  * auto-growing, as in the
                                                  * next line. */

    if(tpmsel->sizeOfSelect < i/8+1) { tpmsel->sizeOfSelect = i/8+1; } /* XXX not future-proof */
    /* Set the bit corresponding to PCR i */
    tpmsel->pcrSelect[i/8] |= (1 << (i%8));
}

bool utpm_pcr_is_selected(TPM_PCR_SELECTION *tpmsel, uint32_t i) {
    /* TODO: fail loudly if any of these conditions do not hold */
    if(NULL == tpmsel) return false;
    if(i >= TPM_PCR_NUM) return false;
    if(i/8 >= tpmsel->sizeOfSelect) return false;

    return (tpmsel->pcrSelect[i/8] & (1 << (i%8)));
}


/**
 * Return the amount of space overhead (in bytes) expected when
 * 'inlen' bytes of plaintext are sealed to the PCRs specified in
 * 'tpmsel'.
 *
 * NOTE: This _must_ remain consistent with the logic in utpm_seal().
 *
 * TODO: Refactor utpm_seal() to have a size-only operating mode
 * (i.e., when certain input parameters are NULL).  It will be
 * reasonable to change this function into a wrapper to call
 * utpm_seal() with NULL buffers once that refactoring is complete.
 */

unsigned int utpm_seal_output_size(unsigned int inlen,
                                                 bool usingPcrs)
{
    unsigned int pad, size = 0;

    /**
     * 6 Contributors:
     * 0. IV for symmetric encryption
     * 1. TPM_PCR_SELECTION (two cases: 0 PCRs, 1+ PCRs)
     * 2. input_len
     * 3. input itself
     * 4. pad out to symmetric encryption block size
     * 5. SHA1-HMAC
     */

    /* 0 */
    size += TPM_AES_KEY_LEN_BYTES;
    /* 1 */
    size += usingPcrs ? sizeof(TPM_PCR_INFO) : sizeof(uint16_t);
    /* 2 */
    size += sizeof(uint32_t);
    /* 3 */
    size += inlen;
    /* 4 */
    pad = ALIGN_UP(size, TPM_AES_KEY_LEN_BYTES) - size;
    size += pad;
    /* 5 */
    size += TPM_HASH_SIZE;

    return size;
}
