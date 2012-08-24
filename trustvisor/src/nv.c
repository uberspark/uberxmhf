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

#include <xmhf.h> 

#include <stdbool.h>

#include <scode.h> /* copy_from_guest */
#include <random.h> /* rand_bytes_or_die() */
#include <nv.h>

#include <tv_log.h>

/* defined in scode.c */
/* TODO: more elegant organization of these data structures */
extern int *scode_curr;
extern whitelist_entry_t *whitelist;


/**
 * XXX REDUNDANT; identical logic exists in tv_utpm.h. Useful
 * primitives may exist in bitfield.h.
 *
 * TODO: Consolidate.
 */
static inline bool pcr_is_selected(tpm_pcr_selection_t *tpmsel, uint32_t i) {
  ASSERT(NULL != tpmsel);
		
  if(i/8 >= tpmsel->size_of_select) return false;

  return (tpmsel->pcr_select[i/8] & (1 << (i%8)));
}

static void dump_pcr_info_short(tpm_pcr_info_short_t *info) {
  unsigned int i;
  ASSERT(NULL != info);

  /* pcr_selection */
  eu_trace("selected PCRs:");
  for(i=0; i<24; i++) {
    if(pcr_is_selected(&info->pcr_selection, i)) {
      eu_trace("pcr %d, ", i);						
    }
  }

  /* locality_at_release */
  eu_trace("localityAtRelease  ");
  for(i=0; i<=4; i++) {
    if(1<<i & info->locality_at_release) {
      eu_trace("locality %d, ", i);
    }
  }
  /* digest_at_release */
  eu_trace("digestAtRelease %*D",
           sizeof(info->digest_at_release),
           info->digest_at_release.digest,
           " ");

}

static void dump_nv_data_public(tpm_nv_data_public_t *pub) {
  ASSERT(NULL != pub);

  eu_trace("nvIndex              "
          "0x%08x", pub->nv_index);

  /* pcrInfoRead, pcrInfoWrite */
  eu_trace("pcrInfoRead:         ");
  dump_pcr_info_short(&pub->pcr_info_read);
  eu_trace("pcrInfoWrite:        ");
  dump_pcr_info_short(&pub->pcr_info_write);

  eu_trace("  permission           0x%08x",	pub->permission.attributes);

  eu_trace("bReadSTClear         %s",
           pub->b_read_st_clear ? "true" : "false");
  eu_trace("bWriteSTClear        %s",
           pub->b_write_st_clear ? "true" : "false");
  eu_trace("bWriteDefine         %s",
           pub->b_write_define ? "true" : "false");

  eu_trace("data_size            %d",	pub->data_size);
}

/**
 * Ensure that the provided NV index is access controlled based on
 * Locality 2 and PCRs 17 and 18.  FIXME: PCR access control is almost
 * certainly not this simple!
 *
 * Returns: 0 on success.
 */
static int validate_nv_access_controls(unsigned int locality,
                                       tpm_nv_index_t idx) {
  tpm_nv_data_public_t pub;
  int rv = 1;

  /* Basic sanity-check to protect logic below; we really don't ever
   * expect anything outside of 1--3, and we will probably only ever
   * use 2. */
  ASSERT(locality <= 4);

  EU_CHKN( rv = tpm_get_nv_data_public(locality, idx, &pub));

  dump_nv_data_public(&pub);
		
  /* Confirm a single EXCLUSIVE locality for both reading and writing. */
  EU_CHK((1<<locality == pub.pcr_info_read.locality_at_release)
         && (1<<locality == pub.pcr_info_write.locality_at_release),
         eu_err_e("locality %d !="
                  " locality_at_release", locality));

  /* Confirm MANDATORY PCRs included. */
#define MANDATORY_PCR_A 11 /* XXX 17 */
#define MANDATORY_PCR_B 12 /* XXX 18 */
  eu_err("\nVULNERABILITY:VULNERABILITY:VULNERABILITY:VULNERABILITY\n"
         "   MANDATORY_PCR_x set to unsafe value!!! Proper code\n"
         "   measurement UNIMPLEMENTED for NV index 0x%08x!\n"
         "   Continuing anyways...\n"
         "VULNERABILITY:VULNERABILITY:VULNERABILITY:VULNERABILITY\n",
         idx);

  EU_CHK( pcr_is_selected(&pub.pcr_info_read.pcr_selection, MANDATORY_PCR_A)
          && pcr_is_selected(&pub.pcr_info_read.pcr_selection, MANDATORY_PCR_B)
          && pcr_is_selected(&pub.pcr_info_write.pcr_selection, MANDATORY_PCR_A)
          && pcr_is_selected(&pub.pcr_info_write.pcr_selection, MANDATORY_PCR_B),
          eu_err_e("ERROR: MANDATORY PCRs NOT FOUND in PCR"
                   " Selection for NV index 0x%08x", idx));

  rv = 0;
 out:
  return rv;
}

/**
 * Checks that supplied index is defined, is of the appropriate size,
 * and has appropriate access restrictions in place.  Those are PCRs
 * 17 and 18, and accessible for reading and writing exclusively from
 * locality 2.
 *
 * returns 0 on success.
 */
int validate_trustvisor_nv_region(unsigned int locality,
                                  tpm_nv_index_t idx,
                                  unsigned int expected_size) {
  int rv = 1;
  unsigned int actual_size = 0;

  EU_CHKN( rv = tpm_get_nvindex_size(locality, idx, &actual_size));

  EU_CHK( actual_size == expected_size,
          eu_err_e("ERROR: actual_size (%d) != expected_size (%d)!",
                   actual_size, expected_size));

  EU_CHKN( rv = validate_nv_access_controls(locality, idx),
           eu_err_e("SECURITY ERROR: NV REGION"
                    " ACCESS CONTROL CHECK FAILED for index 0x%08x",
                    idx));

  rv = 0;
 out:
  return rv;
}


/**
 * Take appropriate action to initialize the Micro-TPM's sealed
 * storage facility by populating the MasterSealingSecret based on the
 * contents of the hardware TPM's NVRAM.
 *
 * jtt nv_definespace --index 0x00015213 --size 20 -o tpm -e ASCII \
 * -p 17,18 -w --permission 0x00000000 --writelocality 2 \
 * --readlocality 2
 *
 * returns 0 on success.
 */

static int _trustvisor_nv_get_mss(unsigned int locality, uint32_t idx,
                                  uint8_t *mss, unsigned int mss_size) {
  int rv = 1;
  unsigned int i;
  unsigned int actual_size = mss_size;
  bool first_boot;

  EU_CHKN( rv = validate_trustvisor_nv_region(locality, idx, mss_size));

  EU_CHKN( rv = tpm_nv_read_value(locality, idx, 0, mss, &actual_size));

  EU_CHK( actual_size == mss_size,
          eu_err_e("NVRAM read size %d != MSS expected size %d",
                   actual_size, mss_size));

  /**
   * Check whether the read bytes are all 0xff.  If so, we assume
   * "first-boot" and initialize the contents of NV.
   */
  first_boot = true;
  for(i=0; i<actual_size; i++) {
    if(mss[i] != 0xff) {
      first_boot = false;
      break;
    }
  }

  /* TODO: Get random bytes directly from TPM instead of using PRNG
     (for additional simplicitly / less dependence on PRNG
     security) */
  if(first_boot) {
    eu_trace("first_boot detected!");
    rand_bytes_or_die(mss, mss_size); /* "or_die" is VERY important! */
    EU_CHKN( rv = tpm_nv_write_value(locality, idx, 0, mss, mss_size),
             eu_err_e("ERROR: Unable to write new MSS to TPM NVRAM!"));
  } else {
    eu_trace("MSS successfully read from TPM NVRAM");
  }
    
  rv = 0;
 out:
  return rv;
}

int trustvisor_nv_get_mss(unsigned int locality, uint32_t idx,
                          uint8_t *mss, unsigned int mss_size) {
  int rv = 1;

  ASSERT(NULL != mss);
  ASSERT(mss_size >= 20); /* Sanity-check security level wrt SHA-1 */

  eu_trace("locality %d, idx 0x%08x, mss@%p, mss_size %d",
           locality, idx, mss, mss_size);

  EU_CHKN( rv = _trustvisor_nv_get_mss(locality, idx, mss, mss_size));

  rv = 0;
 out:
  if (rv) {
    /**
     * Something went wrong in the optimistic attempt to read /
     * initialize the MSS.  If configured conservatively, halt now!
     */
    if(HALT_UPON_NV_PROBLEM) {
      eu_err("MasterSealingSeed initialization FAILED! SECURITY HALT!");

      HALT();
    }

    /**
     * If we're still here, then we're configured to attempt to run in a
     * degraded "ephemeral" mode where there is no long-term (across
     * reboots) sealing support.  Complain loudly.  We will still halt
     * if random keys are not available.
     */
    eu_err("MasterSealingSeed initialization FAILED!\n"
           "Continuing to operate in degraded mode. EPHEMERAL SEALING ONLY!");
    rand_bytes_or_die(mss, mss_size);
  
    /* XXX TODO: Eliminate degraded mode once we are sufficiently robust
       to support development and testing without it. */
  }
  return 0;  
}


/**
 * **********************************************************
 * NV functions specific to Rollback Resistance follow.
 *
 * This includes functions that handle hypercalls.
 *
 * jtt nv_definespace --index 0x00014e56 --size 32 \
 *     -o tpm -e ASCII \
 *     -p 11,12 \
 *     -w --permission 0x00000000 --writelocality 2 --readlocality 2
 *
 * **********************************************************
 */

/**
 * Only one PAL on the entire system is granted privileges to
 * {getsize|readall|writeall} the actual hardware TPM NV Index
 * dedicated to rollback resistance.  This is the NVRAM Multiplexor
 * PAL, or NvMuxPal.
 *
 * The purpose of this function is to make sure that a PAL that is
 * trying to make one of those hypercalls is actually the PAL that is
 * authorized to do so.
 *
 * Returns: 0 on success, non-zero otherwise.
 * TODO: Define some more meaningful failure codes.
 */
static uint32_t authenticate_nv_mux_pal(VCPU *vcpu) {
  uint32_t rv = 1;
  TPM_DIGEST pcr;
  const int pcr_idx = 0;
  eu_pulse();

  /* make sure that this vmmcall can only be executed when a PAL is
   * running */
  EU_CHK( scode_curr[vcpu->id] != -1,
          eu_err_e("GenRandom ERROR: no PAL is running!"));

  /* Read uTPM PCR[0] */
  EU_CHKN( rv = utpm_pcrread(&pcr, &whitelist[scode_curr[vcpu->id]].utpm, pcr_idx));

  if(!g_nvenforce) {
    /* Boot param (cmdline) explicitly said not to enforce that only
     * one anointed PAL shall be the NvMuxPal.  Make some warning
     * noise in the log anyways, just in case this is accidental. */
    eu_warn("\n\n"
            "WARNING:WARNING:WARNING:WARNING:WARNING:WARNING\n"
            "   NvMuxPal Authentication DISABLED!!!\n"
            "   Any PAL can manipulate sensitive NV areas!!!\n"
            "   This may be a VULNERABILITY!!!\n"
            "   Continuing anyways...\n"
            "WARNING:WARNING:WARNING:WARNING:WARNING:WARNING\n");

    /* Useful to see whether enforcement would have allowed access */
    print_hex("g_nvpalpcr0:  ", g_nvpalpcr0, sizeof(g_nvpalpcr0));
    print_hex("actual PCR[0]: ", pcr.value, sizeof(pcr.value));

    return 0; /* "success" */
  }

  /**
   * If we are here, then g_nvenforce is true, and we must ensure that
   * the PAL attempting to access the hardware TPM's NV-RAM matches
   * the one specified in g_nvpalpcr0.
   */

  EU_CHKN( rv = memcmp(g_nvpalpcr0, pcr.value, sizeof(pcr.value)),
           eu_warn_e("SECURITY WARNING: Disallowed PAL Attempted to access TPM NV-RAM"));

  eu_trace("Attempt to access TPM NV-RAM APPROVED.");
  rv = 0;
 out:
  return rv;
}

uint32_t hc_tpmnvram_getsize(VCPU* vcpu, uint32_t size_addr) {
  uint32_t rv = 1;
  uint32_t actual_size;

  eu_pulse();

  /* Make sure the asking PAL is authorized */
  EU_CHKN( rv = authenticate_nv_mux_pal(vcpu));

  /* Open TPM */
  /* TODO: Make sure this plays nice with guest OS */
  EU_CHKN( rv = emhf_tpm_open_locality(TRUSTVISOR_HWTPM_NV_LOCALITY),
           eu_err_e("FATAL ERROR: Could not access HW TPM."));

  /* Make the actual TPM call */
  EU_CHKN( rv = tpm_get_nvindex_size(TRUSTVISOR_HWTPM_NV_LOCALITY,
                                     HW_TPM_ROLLBACK_PROT_INDEX, &actual_size));

  /* Close TPM */
  emhf_tpm_deactivate_all_localities();

  eu_trace("HW_TPM_ROLLBACK_PROT_INDEX 0x%08x size"
          " = %d", HW_TPM_ROLLBACK_PROT_INDEX, actual_size);

  EU_CHKN( copy_to_current_guest(vcpu, size_addr, &actual_size, sizeof(actual_size)));

  rv = 0;
 out:
  return rv;
}

uint32_t hc_tpmnvram_readall(VCPU* vcpu, uint32_t out_addr) {
  uint32_t rv = 1;
  uint32_t data_size = HW_TPM_ROLLBACK_PROT_SIZE;
  uint8_t data[HW_TPM_ROLLBACK_PROT_SIZE];
  bool opened_tpm = false;

  eu_pulse();

  /* Make sure the asking PAL is authorized */
  EU_CHKN( rv = authenticate_nv_mux_pal(vcpu));

  /* Open TPM */
  /* TODO: Make sure this plays nice with guest OS */
  EU_CHKN( rv = emhf_tpm_open_locality(TRUSTVISOR_HWTPM_NV_LOCALITY));
  opened_tpm = true;

  /* Make the actual TPM call */
  EU_CHKN( rv = tpm_nv_read_value(TRUSTVISOR_HWTPM_NV_LOCALITY,
                                  HW_TPM_ROLLBACK_PROT_INDEX, 0,
                                  data,
                                  &data_size));

  EU_CHK( HW_TPM_ROLLBACK_PROT_SIZE == data_size,
          rv = 1, /* TODO: define some meaningful error values */
          eu_err_e("ERROR: HW_TPM_ROLLBACK_PROT_SIZE (%d) !="
                   " data_size (%d)",
                   HW_TPM_ROLLBACK_PROT_SIZE, data_size));

  EU_CHKN( copy_to_current_guest(vcpu, out_addr, data, HW_TPM_ROLLBACK_PROT_SIZE));
  
  rv = 0;
 out:
  /* Close TPM */
  if (opened_tpm) {
    emhf_tpm_deactivate_all_localities();
  }

  return rv;
}

uint32_t hc_tpmnvram_writeall(VCPU* vcpu, uint32_t in_addr) {
  uint32_t rv = 1;
  uint8_t data[HW_TPM_ROLLBACK_PROT_SIZE];
  bool opened_tpm = false;
		
  eu_pulse();

  /* Make sure the asking PAL is authorized */
  EU_CHKN( rv = authenticate_nv_mux_pal(vcpu));

  /* Open TPM */
  /* TODO: Make sure this plays nice with guest OS */
  EU_CHKN( rv = emhf_tpm_open_locality(TRUSTVISOR_HWTPM_NV_LOCALITY));
  opened_tpm = true;

  /* copy input data to host */
  EU_CHKN( copy_from_current_guest(vcpu, data, in_addr, HW_TPM_ROLLBACK_PROT_SIZE));
		
  /* Make the actual TPM call */
  EU_CHKN( rv = tpm_nv_write_value(TRUSTVISOR_HWTPM_NV_LOCALITY,
                                   HW_TPM_ROLLBACK_PROT_INDEX, 0,
                                   data,
                                   HW_TPM_ROLLBACK_PROT_SIZE));

  rv = 0;
 out:
  /* Close TPM */
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
