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
 * utpm common functions
 * adapted from trustvisor utpm by amit vasudevan (amitvasudevan@acm.org
 */

//#include <types.h>
//#include <arm8-32.h>
//#include <bcm2837.h>
//#include <miniuart.h>
//#include <debug.h>
#include <uberspark/include/uberspark.h>
#include <uberspark/uobjrtl/crt/include/string.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/libutpm/utpm.h>


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
        uberspark_uobjrtl_crt__memcpy(dest, pcrSelection, *bytes_consumed);
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
            uberspark_uobjrtl_crt__memcpy(dest + *bytes_consumed, pcrInfo->digestAtRelease.value, TPM_HASH_SIZE);
            *bytes_consumed += TPM_HASH_SIZE;

            uberspark_uobjrtl_crt__memcpy(dest + *bytes_consumed, pcrInfo->digestAtCreation.value, TPM_HASH_SIZE);
            *bytes_consumed += TPM_HASH_SIZE;
        }
    }
    return 0;
}



/* FIXME: place this somewhere appropriate */
uint32_t utpm_ntohl(uint32_t in) {
    uint8_t *s = (uint8_t *)&in;
    return (uint32_t)(s[0] << 24 | s[1] << 16 | s[2] << 8 | s[3]);
}



/**
 * Create the current TPM_PCR_COMPOSITE for uTPM PCR values
 * specified by TPM_PCR_SELECTION.
 *
 */
//static uint32_t utpm_internal_allocate_and_populate_current_TpmPcrComposite(
//    utpm_master_state_t *utpm,
//    TPM_PCR_SELECTION *tpmsel,
//    uint8_t **tpm_pcr_composite,
//    uint32_t *space_needed_for_composite
//    )
uint32_t utpm_internal_allocate_and_populate_current_TpmPcrComposite(
    utpm_master_state_t *utpm,
    TPM_PCR_SELECTION *tpmsel,
    uint8_t *tpm_pcr_composite,
    uint32_t *space_needed_for_composite
    )
{
    uint32_t rv = 0;
    uint32_t i;
    uint32_t num_pcrs_to_include = 0;
    uint8_t *p = NULL;

    if(!utpm || !tpmsel || !tpm_pcr_composite || !space_needed_for_composite) return 1;

    //dprintf(LOG_TRACE, "[TV:UTPM] %s: tpmsel->sizeOfSelect %d\n",
    //        __FUNCTION__, tpmsel->sizeOfSelect);
    //print_hex("  tpmsel->pcrSelect: ", tpmsel->pcrSelect, tpmsel->sizeOfSelect);
    for(i=0; i<TPM_PCR_NUM; i++) {
        if(utpm_pcr_is_selected(tpmsel, i)) {
            num_pcrs_to_include++;
        }
        //dprintf(LOG_TRACE, "    uPCR-%d: %s\n", i,
        //        utpm_pcr_is_selected(tpmsel, i) ? "included" : "excluded");
    }

    /**
     * Construct TPM_COMPOSITE structure that will summarize the relevant PCR values
     */

    /* Allocate space for the necessary number of uPCR values */
    // TPM_PCR_COMPOSITE contains TPM_PCR_SELECTION + n*TPM_HASH_SIZE PCR values

    /* struct TPM_PCR_COMPOSITE {
         TPM_PCR_SELECTION select;
         uint32_t valueSize;
         [size_is(valueSize)] TPM_PCRVALUE pcrValue[];
       };
    */
    *space_needed_for_composite =
        sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect + /* TPM_PCR_COMPOSITE.select */
        sizeof(uint32_t) +                                    /* TPM_PCR_COMPOSITE.valueSize */
        num_pcrs_to_include * TPM_HASH_SIZE;                  /* TPM_PCR_COMPOSITE.pcrValue[] */

    if ( (*space_needed_for_composite) > MAX_PCR_COMPOSITE_SIZE )
    	return 1;

    //dprintf(LOG_TRACE, "  sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect = %d\n",
    //        sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect);
    //dprintf(LOG_TRACE, "  sizeof(uint32_t)                                    = %d\n",
    //        sizeof(uint32_t));
    //dprintf(LOG_TRACE, "  num_pcrs_to_include * TPM_HASH_SIZE                 = %d\n",
    //        num_pcrs_to_include * TPM_HASH_SIZE);
    //dprintf(LOG_TRACE, "  ---------------------------------------------------------\n");
    //dprintf(LOG_TRACE, "  *space_needed_for_composite                         = %d\n",
    //        *space_needed_for_composite);

    //if(NULL == (*tpm_pcr_composite = malloc(*space_needed_for_composite))) {
    //    dprintf(LOG_ERROR, "[TV:UTPM] malloc(%d) failed!\n", *space_needed_for_composite);
    //    return 1;
    //}

    /** Populate TPM_COMPOSITE buffer **/
    //p = *tpm_pcr_composite;
    p = tpm_pcr_composite;

    /* 1. TPM_PCR_COMPOSITE.select */
    uberspark_uobjrtl_crt__memcpy(p, tpmsel, sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect);
    p += sizeof(tpmsel->sizeOfSelect) + tpmsel->sizeOfSelect;
    /* 2. TPM_PCR_COMPOSITE.valueSize (big endian # of bytes (not # of PCRs)) */
    *((uint32_t*)p) = utpm_ntohl(num_pcrs_to_include*TPM_HASH_SIZE);
    p += sizeof(uint32_t);
    /* 3. TPM_PCR_COMPOSITE.pcrValue[] */
    for(i=0; i<TPM_PCR_NUM; i++) {
        if(utpm_pcr_is_selected(tpmsel, i)) {
            uberspark_uobjrtl_crt__memcpy(p, utpm->pcr_bank[i].value, TPM_HASH_SIZE);
            //dprintf(LOG_TRACE, "  PCR-%d: ", i);
            //print_hex(NULL, p, TPM_HASH_SIZE);
            p += TPM_HASH_SIZE;
        }
    }

    /* TODO: Assert */
    //if((uint32_t)p-(uint32_t)(*tpm_pcr_composite) != *space_needed_for_composite) {
    if((uint32_t)p-(uint32_t)(tpm_pcr_composite) != *space_needed_for_composite) {

    	//dprintf(LOG_ERROR, "[TV:UTPM] ERROR! (uint32_t)p-(uint32_t)*tpm_pcr_composite "
        //        "!= space_needed_for_composite\n");
        rv = 1; /* FIXME: Indicate internal error */
        goto out;
    }

    //print_hex(" TPM_PCR_COMPOSITE: ", *tpm_pcr_composite, *space_needed_for_composite);
  out:
    return rv;

}




/**
 * TPM_PCR_COMPOSITE is created by reading the current value of the
 * PCRs mentioned in TPM_PCR_SELECTION.
 *
 * It does not make sense to call this function if the
 * TPM_PCR_SELECTION does not select anything.
 */
TPM_RESULT utpm_internal_digest_current_TpmPcrComposite(
    utpm_master_state_t *utpm,
    TPM_PCR_SELECTION *pcrSelection,
    TPM_COMPOSITE_HASH *digest)
{
    uint32_t space_needed_for_composite = 0;
    uint8_t buf_tpm_pcr_composite[MAX_PCR_COMPOSITE_SIZE];
    uint8_t *tpm_pcr_composite = &buf_tpm_pcr_composite;
    uint32_t rv = 0;

    if(!utpm || !pcrSelection || !digest) { return 1; }

    if(pcrSelection->sizeOfSelect < 1) { return 1; }

    rv = utpm_internal_allocate_and_populate_current_TpmPcrComposite(
        utpm,
        pcrSelection,
        tpm_pcr_composite,
        &space_needed_for_composite);

    if(0 != rv) { return 1; }

    //sha1_buffer(tpm_pcr_composite, space_needed_for_composite, digest->value);
    uberspark_uobjrtl_crypto__hashes_sha1__sha1_memory(tpm_pcr_composite, space_needed_for_composite, digest->value, TPM_HASH_SIZE);

    //if(tpm_pcr_composite) { free(tpm_pcr_composite); tpm_pcr_composite = NULL; }

    return rv;
}


/**
 * Best effort to populate an array of *len random-bytes.  Returns 0
 * on success, otherwise returns the number of bytes that were
 * actually available (and updates *len).
 */
int utpm_rand_bytes(uint8_t *out, unsigned int *len) {
    int rv=1;

    //TBD: plug in random number generation

    /* even here we do not want to tolerate failure to initialize */
    //EU_VERIFY( g_master_prng_init_completed);

    //EU_VERIFY( out);
    //EU_VERIFY( len);
    //EU_VERIFY( *len >= 1);

    /* at the present time this will either give all requested bytes
     * or fail completely.  no support for partial returns, though
     * that may one day be desirable. */
    //EU_VERIFYN( reseed_ctr_drbg_using_tpm_entropy_if_needed());

    //EU_CHKN( rv = nist_ctr_drbg_generate(&g_drbg, out, *len, NULL, 0));

    //eu_trace("Successfully generated %d pseudo-random bytes", *len);

    rv=0;
 out:
    return rv;
}

