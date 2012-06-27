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
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
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

#include <xmhf.h> 

#include <stdbool.h>

#include <tv_utpm.h>
#include <nist_ctr_drbg.h>
#include <random.h> 

#include <crypto_init.h>
#include <nv.h>

#include <tommath.h>

#include <tv_log.h>

/* FIXME: make them static (i.e., only inside this file) */
/* extern */ bool g_master_prng_init_completed = false;
/* extern */ bool g_master_crypto_init_completed = false;

/**
 * These two are set by the boot cmdline-parsing code in appmain.c,
 * and used primarily from within nv.c.  Defining them here so as to
 * have such globals in one place. */
/* extern */ bool g_nvenforce = true;
/* extern */ uint8_t g_nvpalpcr0[20];

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
  uint32_t rv=1;
  unsigned int actual_len;

  EU_CHK( buf);

  actual_len = requested_len;
  EU_CHKN( rv = tpm_get_random(CRYPTO_INIT_LOCALITY, buf, &actual_len));

  /* TODO: Try a few more times before giving up. */
  EU_CHK( actual_len == requested_len,
          eu_err_e("FATAL ERROR: Could not access TPM to initialize PRNG."));

  eu_trace("Successfully received %d/%d bytes of entropy from HW TPM.",
           actual_len, requested_len);

  rv=0;
 out:
  return rv;
}


/* returns 0 on success. */
static int master_prng_init(void) {
  uint8_t EntropyInput[CTR_DRBG_SEED_BITS/8];
  uint64_t Nonce;
  int rv=1;

  EU_CHKN( nist_ctr_initialize());

  /* Get CTR_DRBG_SEED_BITS of entropy from the hardware TPM */
  EU_VERIFYN( get_hw_tpm_entropy( EntropyInput, CTR_DRBG_SEED_BITS/8),
              eu_err_e("FATAL ERROR: Could not access TPM to initialize PRNG."));

  /* Use rdtsc to get CTR_DRBG_NONCE_BITS of initialization nonce */
  COMPILE_TIME_ASSERT(CTR_DRBG_NONCE_BITS/8 == sizeof(Nonce));
  Nonce = rdtsc64();

  EU_VERIFYN( nist_ctr_drbg_instantiate(&g_drbg, EntropyInput, sizeof(EntropyInput),
                                        &Nonce, sizeof(Nonce), NULL, 0),
              eu_err_e("FATAL ERROR: nist_ctr_drbg_instantiate FAILED."));

  /* set up the libtomcrypt prng wrapper */
  g_ltc_prng_id = register_prng( &tv_sprng_desc);
  EU_CHK( g_ltc_prng_id >= 0);

  rv=0;
 out:
  return rv;
}

/**
 * Do a measurement of the "quick and dirty" RSA public key from the
 * keypair used to sign uTPM quotes, effectively "bridging" trust from
 * the hardware TPM to the software keys in TrustVisor.
 *
 * returns 0 on success.
 */
#define QND_BRIDGE_PUBKEY_PCR     19

static int trustvisor_measure_qnd_bridge_signing_pubkey( void ) {
  int rv=1;
  uint32_t serial_pubkey_len=0;
  uint8_t *serial_pubkey = NULL;
  tpm_digest_t digest;
  tpm_pcr_value_t pcr_out;

  /**
   * 1. Serialize RSA key into byte blob for purposes of measurement.
   */
  EU_CHKN( utpm_id_getpub( NULL, &serial_pubkey_len)); /* query for size needed */
  EU_CHK(  serial_pubkey = malloc(serial_pubkey_len));
  EU_CHKN( utpm_id_getpub( serial_pubkey, &serial_pubkey_len));
  eu_trace("Serialized RSA key: %*D", serial_pubkey_len, serial_pubkey, " ");

  /**
   * 2. Hash serialized RSA key.
   */
  EU_CHKN( sha1_buffer( serial_pubkey, serial_pubkey_len, digest.digest));
		
  /**
   * 3. Extend PCR with hash.
   */
  EU_CHKN( rv = tpm_pcr_extend(CRYPTO_INIT_LOCALITY, QND_BRIDGE_PUBKEY_PCR,
                               &digest, &pcr_out),
           eu_err_e("FATAL ERROR: Could not extend HW TPM PCR %d.", QND_BRIDGE_PUBKEY_PCR));

  eu_trace( "Successfully extended HW TPM PCR %d.", QND_BRIDGE_PUBKEY_PCR);
  eu_trace( "New PCR value: ", TPM_HASH_SIZE, pcr_out.digest, " ");

  rv=0;
 out:
  free( serial_pubkey);
  return rv;
}

/* involves accessing TPM NV RAM. */
/* depends on PRNG already being initialized. */
/* returns 0 on success. */
static int trustvisor_long_term_secret_init(void) {
  int rv = 1;
  uint8_t mss[HW_TPM_MASTER_SEALING_SECRET_SIZE];
  /* The actual AES key is smaller than this, so we need a temporary
   * buffer. */
  uint8_t aeskey_temp[HW_TPM_MASTER_SEALING_SECRET_SIZE];
  unsigned long aeskey_temp_len = sizeof(aeskey_temp);
  uint8_t hmackey_temp[HW_TPM_MASTER_SEALING_SECRET_SIZE];
  unsigned long hmackey_temp_len = sizeof(hmackey_temp);
  const uint8_t sealingaes[10] = {0x73, 0x65, 0x61, 0x6c, 0x69, 0x6e,
                                  0x67, 0x61, 0x65, 0x73};
  const uint8_t sealinghmac[11] = {0x73, 0x65, 0x61, 0x6c, 0x69, 0x6e,
                                   0x67,	0x68, 0x6d, 0x61, 0x63};
  rsa_key rsakey;
  int hash_id = register_hash( &sha1_desc);
  
  EU_VERIFY( g_master_prng_init_completed);

  rv = trustvisor_nv_get_mss(CRYPTO_INIT_LOCALITY,
                             HW_TPM_MASTER_SEALING_SECRET_INDEX,
                             mss,
                             HW_TPM_MASTER_SEALING_SECRET_SIZE);
  if(0 != rv) {
    eu_err("FATAL ERROR: trustvisor_nv_get_mss FAILED (%d).\n",
           rv);
    /* TODO: Support degraded operation during development. */
    /* XXX SECURITY XXX: continuing anyways for now */
    //ASSERT(false);
    eu_err( "VULNERABILITY:VULNERABILITY:VULNERABILITY:VULNERABILITY\n"
            "   Reading / initializing master sealing secret FAILED!!\n"
            "   Continuing anyways...\n"
            "VULNERABILITY:VULNERABILITY:VULNERABILITY:VULNERABILITY\n");
  }

  ASSERT( HW_TPM_MASTER_SEALING_SECRET_SIZE == hash_descriptor[hash_id].hashsize);

  /* Derive encryption and MAC keys for sealed storage */
  EU_VERIFYN( hmac_memory( hash_id,
                           mss, HW_TPM_MASTER_SEALING_SECRET_SIZE,
                           sealingaes, sizeof(sealingaes),
                           aeskey_temp, &aeskey_temp_len));

  EU_VERIFYN( hmac_memory( hash_id,
                           mss, HW_TPM_MASTER_SEALING_SECRET_SIZE,
                           sealinghmac, sizeof(sealinghmac),
                           hmackey_temp, &hmackey_temp_len));

  EU_VERIFY( TPM_AES_KEY_LEN_BYTES <= HW_TPM_MASTER_SEALING_SECRET_SIZE);
	
  eu_trace( "Sealing AES key derived from MSS.");
  eu_trace( "Sealing HMAC key derived from MSS.");

  /* /\* SECURITY: Delete these print_hex()'s ASAP! *\/ */
  /* print_hex("XXX mss:       ", mss, 20); */
  /* print_hex("XXX g_aeskey:  ", g_aeskey, (TPM_AES_KEY_LEN>>3)); */
  /* print_hex("XXX g_hmackey: ", g_hmackey, 20); */
    
  /* Initialize RSA key required in uTPM Quote */
  /* FIXME: Having a single key here is a privacy-invading,
   * session-linkable, PAL-linkable hack to get things off the
   * ground. */
  eu_trace( "Generating RSA keypair...");

  /* If someday, somebody decides to keep things going during
     development or debugging, don't forget that we MUST zero
     sensitive keys upon failure. */
  EU_VERIFYN( rsa_make_key( &g_ltc_prng, g_ltc_prng_id, TPM_RSA_KEY_LEN, 65537, &rsakey));
  eu_trace("RSA key pair generated");

  /* same story as above. */
  EU_VERIFYN( utpm_init_master_entropy(aeskey_temp, hmackey_temp, &rsakey));

  rv = 0;
 /* out: */
  memset(mss, 0, HW_TPM_MASTER_SEALING_SECRET_SIZE);
  memset(aeskey_temp, 0, HW_TPM_MASTER_SEALING_SECRET_SIZE);
  memset(hmackey_temp, 0, HW_TPM_MASTER_SEALING_SECRET_SIZE);
  /* Measure the Identity key used to sign Micro-TPM Quotes. */
  /* prefer not to depend on the globals */
  if(0 != (rv = trustvisor_measure_qnd_bridge_signing_pubkey())) {
    eu_err("trustvisor_long_term_secret_init FAILED with rv %d!!!!", rv);
  }
  /* Intentionally not a proper free. Responsibility for this
   * structure has been transferred to the utpm implementation. */
  memset(&rsakey, 0, sizeof(rsakey));

  return rv;
}

/* returns 0 on success. */
/* TODO: take ciphertext input, e.g., from a multiboot_t */
int trustvisor_master_crypto_init(void) {
  int rv=1;
  bool opened_tpm=false;

  /* ensure libtomcrypto's math descriptor is initialized */
  if (!ltc_mp.name) {
    ltc_mp = ltm_desc;
  }

  EU_CHKN( rv = emhf_tpm_open_locality(CRYPTO_INIT_LOCALITY),
           eu_err_e( "FATAL ERROR: Could not access HW TPM."));
  opened_tpm=true;
		
  /* PRNG */
  EU_CHKN( rv = master_prng_init(),
           eu_err_e( "AES-256 CTR_DRBG PRNG init FAILED with rv %d!!!!\n", rv));
		
  g_master_prng_init_completed = true;
		
  eu_trace( "AES-256 CTR_DRBG PRNG successfully seeded with TPM RNG.");
        
  /* NV space used to support Micro-TPM Long-Term sealing */
  EU_CHKN( rv = trustvisor_long_term_secret_init());

  eu_trace( "long term secrets initialized successfully.");

  /* Confirm that the NV space that will be used for anti-rollback
     by the NvMuxPal has appropriate controls in place. */
  EU_CHKN( rv = validate_trustvisor_nv_region( TRUSTVISOR_HWTPM_NV_LOCALITY,
                                               HW_TPM_ROLLBACK_PROT_INDEX,
                                               HW_TPM_ROLLBACK_PROT_SIZE),
           eu_err_e( "ERROR: "
                     " validate_trustvisor_nv_region(%d, 0x%08x, %d)"
                     " FAILED with rv %d\n",
                     TRUSTVISOR_HWTPM_NV_LOCALITY,
                     HW_TPM_ROLLBACK_PROT_INDEX,
                     HW_TPM_ROLLBACK_PROT_SIZE,
                     rv),
           rv = 0); /* XXX maintaining old behavior here. is this really what we want? */

  eu_trace( "NvMuxPal anti-rollback NV Region: "
            "Access Controls validated successfully.");
		
  g_master_crypto_init_completed = true;

  /* We're now done with the TPM for a while. Make sure it is
   * available to the legacy OS. */
  rv=0;
 out:
  if (opened_tpm) {
    emhf_tpm_deactivate_all_localities();
  }
		
  return rv;
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:nil */
/* c-basic-offset:2 */
/* End:             */
