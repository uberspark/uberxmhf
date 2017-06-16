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


/* If no destination buffer is provided then just set the number of
 * bytes that would be consumed.*/
uint32_t utpm_internal_memcpy_TPM_PCR_SELECTION(
    TPM_PCR_SELECTION *pcrSelection, uint8_t *dest, uint32_t *bytes_consumed)
{
    if(!pcrSelection || !bytes_consumed) return 1;

    *bytes_consumed = sizeof(pcrSelection->sizeOfSelect) + pcrSelection->sizeOfSelect;

    if(dest) {
        memcpy(dest, pcrSelection, *bytes_consumed);
    }

    return 0; /* success */
}


/* If no destination buffer is provided then just set the number of
 * bytes that would be consumed.*/
uint32_t utpm_internal_memcpy_TPM_PCR_INFO(
    TPM_PCR_INFO *pcrInfo, /* in */
    uint8_t *dest, /* out */
    uint32_t *bytes_consumed) /* out */
{
    uint32_t rv;

    if(!pcrInfo || !bytes_consumed) { return 1; }

    rv = utpm_internal_memcpy_TPM_PCR_SELECTION(&pcrInfo->pcrSelection, dest, bytes_consumed);
    if(0 != rv) { return rv; }


    if(pcrInfo->pcrSelection.sizeOfSelect > 0) {
        /* If no destination buffer, then just return the required
         * size in bytes_consumed. */
        if(NULL == dest) {
            *bytes_consumed += 2*TPM_HASH_SIZE;
            return 0;
        }
        /* If we're still here, copy two TPM_COMPOSITE_HASH values to dest. */
        else {
            memcpy(dest + *bytes_consumed, pcrInfo->digestAtRelease.value, TPM_HASH_SIZE);
            *bytes_consumed += TPM_HASH_SIZE;

            memcpy(dest + *bytes_consumed, pcrInfo->digestAtCreation.value, TPM_HASH_SIZE);
            *bytes_consumed += TPM_HASH_SIZE;
        }
    }
    return 0;
}
