/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

/**
 * Initialize critical TrustVisor cryptography.
 *
 * Author: Jonathan McCune
 */

#include <emhf.h> 

#include <stdbool.h>

#include <tv_utpm.h>
#include <nist_ctr_drbg.h>
#include <random.h> 

#include <crypto_init.h>
#include <nv.h>
#include <sha1.h>
#include <hmac.h>
#include <rsa.h>

/* awesome trick from http://www.jaggersoft.com/pubs/CVu11_3.html */
#define COMPILE_TIME_ASSERT(pred)               \
  switch(0){case 0:case pred:;}

/* FIXME: make them static (i.e., only inside this file) */
/* extern */ bool g_master_prng_init_completed = false;
/* extern */ bool g_master_crypto_init_completed = false;

/* XXX FIXME: needs spinlock protection in MP mode */
/* extern */ NIST_CTR_DRBG g_drbg; 

/* Don't want to get optimized out. */
void zeroize(uint8_t* _p, unsigned int len) {    
  volatile uint8_t *p = _p;
  unsigned int i;
    
  for(i=0; i<len; i++) {
    ((volatile uint8_t *)p)[i] = 0;
  }
}

#define CRYPTO_INIT_LOCALITY 2

/* If this function fails then our basic security assumptions are
 * violated and TrustVisor should HALT! */
/* returns 0 on success. */
int get_hw_tpm_entropy(uint8_t* buf, unsigned int requested_len /* bytes */) {
  uint32_t rv;
  unsigned int actual_len;
		
  if(!buf) { return 1; }

  actual_len = requested_len;
  rv = tpm_get_random(CRYPTO_INIT_LOCALITY, buf, &actual_len);

  if(actual_len != requested_len) {
    dprintf(LOG_ERROR, "\nFATAL ERROR: Could not access TPM to initialize PRNG.\n");
    /* TODO: Try a few more times before giving up. */
    return 1;
  }

  dprintf(LOG_TRACE, "\n[TV] Successfully received %d/%d bytes of entropy from HW TPM.",
          actual_len, requested_len);

  return 0;
}


/* returns 0 on success. */
static int master_prng_init(void) {
  uint8_t EntropyInput[CTR_DRBG_SEED_BITS/8];
  uint64_t Nonce;
    
  nist_ctr_initialize();

  /* Get CTR_DRBG_SEED_BITS of entropy from the hardware TPM */
  if(get_hw_tpm_entropy(EntropyInput, CTR_DRBG_SEED_BITS/8)) {
    dprintf(LOG_ERROR, "\nFATAL ERROR: Could not access TPM to initialize PRNG.\n");
    HALT();
    return 1;
  }

  /* Use rdtsc to get CTR_DRBG_NONCE_BITS of initialization nonce */
  COMPILE_TIME_ASSERT(CTR_DRBG_NONCE_BITS/8 == sizeof(Nonce));
  Nonce = rdtsc64();

  if(0 != nist_ctr_drbg_instantiate(&g_drbg, EntropyInput, sizeof(EntropyInput),
                                    &Nonce, sizeof(Nonce), NULL, 0)) {
    dprintf(LOG_ERROR, "\nFATAL ERROR: nist_ctr_drbg_instantiate FAILED.\n");
    HALT();
    return 1;
  }				

  return 0;
}


/**
 * Do a measurement of the "quick and dirty" RSA public key from the
 * keypair used to sign uTPM quotes, effectively "bridging" trust from
 * the hardware TPM to the software keys in TrustVisor.
 *
 * returns 0 on success.
 */
#define QND_BRIDGE_PUBKEY_PCR     19
#define SERIAL_BUFSIZE (TPM_RSA_KEY_LEN + 2*sizeof(uint32_t))

static int trustvisor_measure_qnd_bridge_signing_pubkey(rsa_context *rsa) {
  int rv;
  uint8_t serial_pubkey[SERIAL_BUFSIZE];
  tpm_digest_t digest;
  tpm_pcr_value_t pcr_out;
		
  if(NULL == rsa) {
    dprintf(LOG_ERROR, "\nERROR: NULL rsa context.\n");
    return 1;
  }

  /**
   * 1. Serialize RSA key into byte blob for purposes of measurement.
   */
  /* len (4 bytes, big endian) | E (4 bytes, big endian) | N (XXX bytes, big endian)*/
  memset(serial_pubkey, 0, SERIAL_BUFSIZE);
  /* rsa->len */
  *((uint32_t*)&serial_pubkey[0]) = NIST_HTONL(rsa->len);
  /* rsa->E */
  if(0 != mpi_write_binary(&rsa->E, &serial_pubkey[0]+sizeof(uint32_t), sizeof(uint32_t))) {
    dprintf(LOG_ERROR, "\nERROR: mpi_write_binary FAILED with rsa->E.\n");
    return 1;
  }
  /* rsa->N */
  if(rsa->len != TPM_RSA_KEY_LEN) {
    dprintf(LOG_ERROR, "\nERROR: rsa->len != TPM_RSA_KEY_LEN.\n");
    return 1;
  }
  if(0 != mpi_write_binary(&rsa->N, &serial_pubkey[0]+2*sizeof(uint32_t), rsa->len)) {
    dprintf(LOG_ERROR, "\nERROR: mpi_write_binary FAILED with rsa->N.\n");
    return 1;
  }
  print_hex("[TV] Serialized RSA key: ", serial_pubkey, SERIAL_BUFSIZE);

  /**
   * 2. Hash serialized RSA key.
   */
  if(0 != sha1_buffer(serial_pubkey, SERIAL_BUFSIZE, digest.digest)) {
    return 1;
  }
  print_hex("Hashed serialized RSA key: ", digest.digest, TPM_HASH_SIZE);
		
  /**
   * 3. Extend PCR with hash.
   */
  rv = tpm_pcr_extend(CRYPTO_INIT_LOCALITY, QND_BRIDGE_PUBKEY_PCR,
                      &digest, &pcr_out);
  if(0 != rv) {
    dprintf(LOG_ERROR, "\nFATAL ERROR: Could not extend HW TPM PCR %d.\n", QND_BRIDGE_PUBKEY_PCR);
    return rv;
  }

  dprintf(LOG_TRACE, "\n[TV] Successfully extended HW TPM PCR %d.\n", QND_BRIDGE_PUBKEY_PCR);
  print_hex("[TV] New PCR value: ", pcr_out.digest, TPM_HASH_SIZE);

  return 0;
}

/* involves accessing TPM NV RAM. */
/* depends on PRNG already being initialized. */
/* returns 0 on success. */
static int trustvisor_long_term_secret_init(void) {
  int rv = 0;
  uint8_t mss[HW_TPM_MASTER_SEALING_SECRET_SIZE];
  /* The actual AES key is smaller than this, so we need a temporary
   * buffer. */
  uint8_t aeskey_temp[HW_TPM_MASTER_SEALING_SECRET_SIZE];
  uint8_t hmackey_temp[HW_TPM_MASTER_SEALING_SECRET_SIZE];
  const uint8_t sealingaes[10] = {0x73, 0x65, 0x61, 0x6c, 0x69, 0x6e,
                                  0x67, 0x61, 0x65, 0x73};
  const uint8_t sealinghmac[11] = {0x73, 0x65, 0x61, 0x6c, 0x69, 0x6e,
                                   0x67,	0x68, 0x6d, 0x61, 0x63};
  rsa_context rsa;
	
  ASSERT(true == g_master_prng_init_completed);

  rv = trustvisor_nv_get_mss(CRYPTO_INIT_LOCALITY,
                             HW_TPM_MASTER_SEALING_SECRET_INDEX,
                             mss,
                             HW_TPM_MASTER_SEALING_SECRET_SIZE);
  if(0 != rv) {
    dprintf(LOG_ERROR, "\nFATAL ERROR: %s FAILED (%d).\n",
            __FUNCTION__, rv);
    /* TODO: Support degraded operation during development. */
    /* XXX SECURITY XXX: continuing anyways for now */
    //ASSERT(false);
    dprintf(LOG_ERROR, "\n[TV] %s: \n\n"
            "VULNERABILITY:VULNERABILITY:VULNERABILITY:VULNERABILITY\n"
            "   Reading / initializing master sealing secret FAILED!!\n"
            "   Continuing anyways...\n"
            "VULNERABILITY:VULNERABILITY:VULNERABILITY:VULNERABILITY\n\n",
            __FUNCTION__);
  }

  COMPILE_TIME_ASSERT(HW_TPM_MASTER_SEALING_SECRET_SIZE == SHA1_RESULTLEN);

  /* Derive encryption and MAC keys for sealed storage */
  HMAC_SHA1(mss, HW_TPM_MASTER_SEALING_SECRET_SIZE,
            sealingaes, sizeof(sealingaes),
            hmackey_temp);
  HMAC_SHA1(mss, HW_TPM_MASTER_SEALING_SECRET_SIZE,
            sealinghmac, sizeof(sealinghmac),
            aeskey_temp);
  ASSERT(TPM_AES_KEY_LEN_BYTES <= HW_TPM_MASTER_SEALING_SECRET_SIZE);
	
  dprintf(LOG_TRACE, "\n[TV] Sealing AES key derived from MSS.");
  dprintf(LOG_TRACE, "\n[TV] Sealing HMAC key derived from MSS.");

  /* /\* SECURITY: Delete these print_hex()'s ASAP! *\/ */
  /* print_hex("XXX mss:       ", mss, 20); */
  /* print_hex("XXX g_aeskey:  ", g_aeskey, (TPM_AES_KEY_LEN>>3)); */
  /* print_hex("XXX g_hmackey: ", g_hmackey, 20); */

    
  /* Initialize RSA key required in uTPM Quote */
  /* FIXME: Having a single key here is a privacy-invading,
   * session-linkable, PAL-linkable hack to get things off the
   * ground. */
  dprintf(LOG_TRACE, "\n[TV] Generating RSA keypair...");
  rsa_init(&rsa, RSA_PKCS_V15, RSA_SHA1);
  if(0 != rsa_gen_key(&rsa, (TPM_RSA_KEY_LEN<<3), 65537)) {
    dprintf(LOG_ERROR, "FAILED!!!!! System halted.");
    /* This is unrecoverable! */
    HALT();
    /* If someday, somebody decides to keep things going during
       development or debugging, don't forget that we MUST zero
       sensitive keys upon failure. */
    rv = 1;
    goto cleanup;
  }
  dprintf(LOG_TRACE, "\n[TV] RSA key pair generated!");

  if(UTPM_SUCCESS != utpm_init_master_entropy(aeskey_temp, hmackey_temp, &rsa)) {
    dprintf(LOG_ERROR, "utpm_init_master_entropy() FAILED!!!!! System halted.");
    HALT();
    /* same story as above. */
    rv = 1;
    goto cleanup;
  }

 cleanup:
  memset(mss, 0, HW_TPM_MASTER_SEALING_SECRET_SIZE);
  memset(aeskey_temp, 0, HW_TPM_MASTER_SEALING_SECRET_SIZE);
  memset(hmackey_temp, 0, HW_TPM_MASTER_SEALING_SECRET_SIZE);
  /* Measure the Identity key used to sign Micro-TPM Quotes. */
  /* prefer not to depend on the globals */
  if(0 != (rv = trustvisor_measure_qnd_bridge_signing_pubkey(&rsa))) {
    dprintf(LOG_ERROR, "\n[TV] trustvisor_long_term_secret_init FAILED with rv %d!!!!\n", rv);
  }
  /* Intentionally not a proper free. Responsibility for this
   * structure has been transferred to the utpm implementation. */
  memset(&rsa, 0, sizeof(rsa_context));

  return rv;
}

/* returns 0 on success. */
/* TODO: take ciphertext input, e.g., from a multiboot_t */
int trustvisor_master_crypto_init(void) {
  int rv;

  if(0 != (rv = hwtpm_open_locality(CRYPTO_INIT_LOCALITY))) {
    dprintf(LOG_ERROR, "\nFATAL ERROR: Could not access HW TPM.\n");
    return rv; /* no need to deactivate */
  }
		
  /* PRNG */
  if(0 != (rv = master_prng_init())) {
    dprintf(LOG_ERROR, "\n[TV] trustvisor_master_crypto_init: "
            "AES-256 CTR_DRBG PRNG init FAILED with rv %d!!!!\n", rv);
    goto out;
  }
		
  g_master_prng_init_completed = true;
		
  dprintf(LOG_TRACE, "\n[TV] trustvisor_master_crypto_init: "
          "AES-256 CTR_DRBG PRNG successfully seeded with TPM RNG.");
        
  /* NV space used to support Micro-TPM Long-Term sealing */
  if(0 != (rv = trustvisor_long_term_secret_init())) {
    dprintf(LOG_ERROR, "\n[TV] trustvisor_long_term_secret_init FAILED with rv %d!!!!\n", rv);
    goto out;
  }

  dprintf(LOG_TRACE, "\n[TV] trustvisor_master_crypto_init: "
          "long term secrets initialized successfully.");

  /* Confirm that the NV space that will be used for anti-rollback
     by the NvMuxPal has appropriate controls in place. */
  if(0 != (rv = validate_trustvisor_nv_region(
                                              TRUSTVISOR_HWTPM_NV_LOCALITY,
                                              HW_TPM_ROLLBACK_PROT_INDEX,
                                              HW_TPM_ROLLBACK_PROT_SIZE))) {
    dprintf(LOG_ERROR, "\n[TV] %s: ERROR: "
            " validate_trustvisor_nv_region(%d, 0x%08x, %d)"
            " FAILED with rv %d\n",	__FUNCTION__,
            TRUSTVISOR_HWTPM_NV_LOCALITY,
            HW_TPM_ROLLBACK_PROT_INDEX,
            HW_TPM_ROLLBACK_PROT_SIZE,
            rv);
    goto out;
  }

  dprintf(LOG_TRACE, "\n[TV] %s: NvMuxPal anti-rollback NV Region"
          "\n     Access Controls validated successfully.", __FUNCTION__);
		
  g_master_crypto_init_completed = true;

  /* We're now done with the TPM for a while. Make sure it is
   * available to the legacy OS. */
 out:
  deactivate_all_localities();
		
  return 0;
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:nil */
/* c-basic-offset:2 */
/* End:             */
