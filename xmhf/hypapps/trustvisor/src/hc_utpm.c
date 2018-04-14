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
 * hc_utpm.c: Handle hypercalls from PALs that invoke uTPM operations.
 *
 * Intention is that TrustVisor needs to contain some "glue" code to
 * connect hypercalls from individual PALs to the uTPM implementation
 * that goes with that PAL.  However, the utpm.[ch] implementation
 * should be sufficiently standalone as to eventually support
 * independent testing.
 *
 * Thus, the purpose of hc_utpm.[ch] is to be the plumbing that
 * connects hypercalls in PALs to the right uTPM operation(s).
 *
 * author: Jon McCune, July 2011
 */

#include <xmhf.h> 

#include <crypto_init.h>
#include <tv_utpm.h> /* formerly utpm.h */
#include <hc_utpm.h>
#include <scode.h> /* copy_from_guest */
#include <malloc.h> /* malloc */

#include <tv_log.h>

/**
 * FIXME: Ugly circular dependency.  hc_utpm.c doesn't work without
 * scode.h, and scode.c doesn't work without hc_utpm.h.  Figure out
 * the hierarchy of dependencies and refactor things more
 * intelligently.
 */

/* defined in scode.c */
/* TODO: more elegant organization of these data structures */
extern int *scode_curr;
extern whitelist_entry_t *whitelist;

uint32_t hc_utpm_seal(VCPU * vcpu, uint32_t input_addr, uint32_t input_len, uint32_t tpmPcrInfo_addr, uint32_t output_addr, uint32_t output_len_addr)
{
	uint8_t indata[MAX_SEALDATA_LEN];  
	uint8_t output[MAX_SEALDATA_LEN]; 
	uint32_t outlen;
	uint32_t rv=1;

	TPM_PCR_INFO tpmPcrInfo;
	
	eu_trace("********** uTPM seal **********");
	eu_trace("input_addr: %x, input_len %d, tpmPcrInfo_addr: %x, output_addr: %x!", input_addr, input_len, tpmPcrInfo_addr, output_addr);

	EU_CHK(	vcpu );
	EU_CHK( input_addr );
	EU_CHK( tpmPcrInfo_addr );
	EU_CHK( output_addr );
	EU_CHK( output_len_addr );

	/**
	 * check input data length
	 */
	/* include seal data header and possible AES encryption padding */
	EU_CHK ( input_len <= (MAX_SEALDATA_LEN - SEALDATA_HEADER_LEN - 16),
		 eu_err_e( "Seal ERROR: input data length is too large, length %#x", input_len));

	/* make sure that this vmmcall can only be executed when a PAL is running */
	EU_CHK ( scode_curr[vcpu->id] != -1,
		 eu_err_e( "Seal ERROR: no PAL is running!"));

	/* copy input data to host */
	EU_CHKN( copy_from_current_guest(vcpu, indata, input_addr, input_len));
	EU_CHKN( copy_from_current_guest(vcpu, (uint8_t*)&tpmPcrInfo, tpmPcrInfo_addr, sizeof(TPM_PCR_INFO)));

	eu_trace("input len = %d!", input_len);
	eu_trace("indata: %*D", input_len, indata, " ");
	eu_trace("tpmPcrInfo: %*D", sizeof(TPM_PCR_INFO), &tpmPcrInfo, " ");

	/* seal, verifying output is not too large */
	EU_CHKN( rv = utpm_seal(&whitelist[scode_curr[vcpu->id]].utpm,
				&tpmPcrInfo,
				indata, input_len,
				output, &outlen));
	EU_CHK( outlen <= MAX_SEALDATA_LEN,
		eu_err_e("Seal ERROR: output data length is too large, lenth %#x", outlen));
	eu_trace("sealedData: %*D", outlen, output, " ");

	/*copy output to guest */
	EU_CHKN( copy_to_current_guest(vcpu, output_addr, output, outlen));

	/* copy out length to guest */
	EU_CHKN( copy_to_current_guest(vcpu,
				       output_len_addr,
				       &outlen,
				       sizeof(outlen)));

	rv = 0;
 out:
	return rv;
}

uint32_t hc_utpm_unseal(VCPU * vcpu, uint32_t input_addr, uint32_t input_len,
			uint32_t output_addr, uint32_t output_len_addr,
			uint32_t digestAtCreation_addr)
{
	uint8_t indata[MAX_SEALDATA_LEN]; 
	uint8_t outdata[MAX_SEALDATA_LEN];
	uint32_t outlen;
	uint32_t ret=1;
	TPM_COMPOSITE_HASH digestAtCreation;

	eu_trace("********** uTPM unseal **********");

	EU_CHK( vcpu);
	EU_CHK( input_addr);
	EU_CHK( output_addr);
	EU_CHK( output_len_addr);
	EU_CHK( digestAtCreation_addr);
	
	eu_trace("input addr: %x, len %d, output addr: %x!",
		 input_addr, input_len, output_addr);
	/* check input data length */
	EU_CHK( input_len <= MAX_SEALDATA_LEN,
		eu_err_e("Unseal ERROR: input data length is too large, length %#x", input_len));

	/* make sure that this vmmcall can only be executed when a PAL is running */
	EU_CHK( scode_curr[vcpu->id] != -1,
		eu_err_e("Unseal ERROR: no PAL is running!"));

	/* copy input data from guest */
	EU_CHKN( copy_from_current_guest( vcpu, indata, input_addr, input_len));

	eu_trace("input data: %*D", input_len, indata, " ");	

	/* unseal */
	EU_CHKN( ret = utpm_unseal(&whitelist[scode_curr[vcpu->id]].utpm, indata, input_len,
				   outdata, &outlen, &digestAtCreation));

	eu_trace("output (unsealed) data: %*D", outlen, outdata, " ");	

	/* check output data length */
	EU_CHK( outlen <= MAX_SEALDATA_LEN,
		eu_err_e("Unseal ERROR: output data length is too large, length %#x", outlen));

	/* copy output to guest */
	EU_CHKN( copy_to_current_guest(vcpu, output_addr, outdata, outlen));
	EU_CHKN( copy_to_current_guest(vcpu, digestAtCreation_addr, (uint8_t*)&digestAtCreation, TPM_HASH_SIZE));
	
	/* copy out length to guest */
	EU_CHKN( copy_to_current_guest( vcpu, output_len_addr, &outlen, sizeof(outlen)));

	ret = 0;
 out:
	return ret;
}


u32 hc_utpm_seal_deprecated(VCPU * vcpu, u32 input_addr, u32 input_len, u32 pcrAtRelease_addr, u32 output_addr, u32 output_len_addr)
{
	unsigned int i;
	u32 outlen;
	u8 pcr[TPM_PCR_SIZE];
	u8 indata[MAX_SEALDATA_LEN];  
	u8 output[MAX_SEALDATA_LEN];
	u32 rv = 1;

	eu_trace("********** uTPM seal DEPRECATED **********");
	eu_trace("input addr: %x, len %d, pcr addr: %x, output addr: %x!",
		 input_addr, input_len, pcrAtRelease_addr, output_addr);

	/* check input data length */
	/* include seal data header and possible AES encryption padding */
	EU_CHK( input_len <= (MAX_SEALDATA_LEN-SEALDATA_HEADER_LEN - 16),
		eu_err_e("Seal ERROR: input data length is too large, length %#x", input_len));

	/* make sure that this vmmcall can only be executed when a PAL is running */
	EU_CHK( scode_curr[vcpu->id] != -1,
		eu_err_e("Seal ERROR: no PAL is running!"));

	/* copy input data to host */
	EU_CHKN( copy_from_current_guest(vcpu, indata, input_addr, input_len));

#if 0
	eu_trace("input len = %d!", input_len);
	eu_trace("input data is:");
	for(i=0;i<input_len;i++) {
		eu_trace("%x ", indata[i]);
	}
	eu_trace("");
#endif

	if (pcrAtRelease_addr != 0) {
		/* seal data to other PAL */
		/* copy pcr value at release to host */
		EU_CHKN( copy_from_current_guest(vcpu, pcr, pcrAtRelease_addr, TPM_PCR_SIZE));
	} else {
		/* seal data to our own */
		/* use current PAL's PCR value */
		eu_trace("get pcr from current PAL's softTPM!");
		memcpy(pcr, whitelist[scode_curr[vcpu->id]].utpm.pcr_bank, TPM_PCR_SIZE);
	}

#if 1
	eu_trace("pcr value is:");
	for(i=0;i<TPM_PCR_SIZE;i++) {
		eu_trace("%x ", pcr[i]);
	}
	eu_trace("");
#endif

	/* seal */
	EU_CHKN( utpm_seal_deprecated(pcr, indata, input_len, output, &outlen));

#if 1
	eu_trace("sealed data len = %d!", outlen);
	eu_trace("sealed data is: ");
	for(i=0;i<outlen;i++) {
		eu_trace("%x ", output[i]);
	}
	eu_trace("");
#endif

	/* check output data length */
	EU_CHK( outlen <= MAX_SEALDATA_LEN,
		eu_err_e("Seal ERROR: output data length is too large, length %#x", outlen));

	/*copy output to guest */
	EU_CHKN( copy_to_current_guest(vcpu, output_addr, output, outlen));

	/* copy out length to guest */
	EU_CHKN( copy_to_current_guest( vcpu, output_len_addr, &outlen, sizeof(outlen)));

	rv=0;
 out:
	return rv;
}

u32 hc_utpm_unseal_deprecated(VCPU * vcpu, u32 input_addr, u32 input_len, u32 output_addr, u32 output_len_addr)
{
	unsigned int i;
	u8 indata[MAX_SEALDATA_LEN]; 
	u8 outdata[MAX_SEALDATA_LEN];
	u32 outlen;
	u32 ret=1;

	eu_trace("********** uTPM unseal DEPRECATED **********");
	eu_trace("input addr: %x, len %d, output addr: %x!", input_addr, input_len, output_addr);

	/* check input data length */
	EU_CHK( input_len <= MAX_SEALDATA_LEN,
		eu_err_e("Unseal ERROR: input data length is too large, length %#x", input_len));

	/* make sure that this vmmcall can only be executed when a PAL is running */
	EU_CHK( scode_curr[vcpu->id] != -1,
		eu_err_e("Seal ERROR: no PAL is running!"));

	/* copy input data from guest */
	EU_CHKN( copy_from_current_guest(vcpu, indata, input_addr, input_len));

#if 0
	eu_trace("input len = %d!", input_len);
	eu_trace("input data is:");
	for(i=0;i<input_len;i++) {
		eu_trace("%x ", indata[i]);
	}
	eu_trace("");
#endif

	/* unseal */
	EU_CHKN( ret = utpm_unseal_deprecated( &whitelist[scode_curr[vcpu->id]].utpm, indata, input_len, outdata, &outlen));

#if 1
	eu_trace("unsealed data len = %d!", outlen);
	eu_trace("unsealed data is: ");
	for(i=0;i<outlen;i++) {
		eu_trace("%x ", outdata[i]);
	}
	eu_trace("");
#endif

	/* check output data length */
	EU_CHK( outlen <= MAX_SEALDATA_LEN,
		eu_err_e("Seal ERROR: output data length is too large, lenth %#x", outlen));

	/* copy output to guest */
	EU_CHKN( copy_to_current_guest(vcpu, output_addr, outdata, outlen));

	/* copy out length to guest */
	EU_CHKN( copy_to_current_guest( vcpu, output_len_addr, &outlen, sizeof(outlen)));

	ret=0;
 out:
	return ret;
}

u32 hc_utpm_quote_deprecated(VCPU * vcpu, u32 nonce_addr, u32 tpmsel_addr, u32 out_addr, u32 out_len_addr)
{
	u8 outdata[TPM_QUOTE_SIZE];
	u8 nonce[TPM_NONCE_SIZE];
	u8 tpmsel[MAX_PCR_SEL_SIZE];
	u32 outlen, ret;
	u32 i, num;
	u32 tpmsel_len;
	uint32_t rsaLen;
	uint8_t rsaModulus[TPM_RSA_KEY_LEN];
	ret=1;

	eu_trace("********** uTPM Quote [DEPRECATED] **********");
	eu_trace("nonce addr: %x, tpmsel addr: %x, output addr %x, outlen addr: %x!", nonce_addr, tpmsel_addr, out_addr, out_len_addr);

	/* make sure that this vmmcall can only be executed when a PAL is running */
	EU_CHK( scode_curr[vcpu->id] != -1,
		eu_err_e("Quote ERROR: no PAL is running!"));

	/* get TPM PCR selection from guest */
	EU_CHKN( copy_from_current_guest( vcpu, &num, tpmsel_addr, sizeof(num)));
	EU_CHK( num <= MAX_PCR_SEL_NUM,
		eu_err_e("Quote ERROR: select too many PCR!"));
	tpmsel_len = 4+4*num;
	eu_trace("%d pcrs are selected!", num);

	EU_CHKN( copy_from_current_guest(vcpu, tpmsel, tpmsel_addr, tpmsel_len));
	for( i=0 ; i< num ; i++ )  {
		EU_CHK( *(((u32 *)(tpmsel+4))+i) < TPM_PCR_NUM,
			eu_err_e("Quote ERROR: bad format of TPM PCR num!"));
	}

	/* get external nonce from guest */
	EU_CHKN( copy_from_current_guest(vcpu, nonce, nonce_addr, TPM_NONCE_SIZE));

#if 1
	eu_trace("external nonce is: ");
	for(i=0;i<TPM_NONCE_SIZE;i++) {
		eu_trace("%x ", nonce[i]);
	}
	eu_trace("");
#endif

	EU_CHKN( ret = utpm_quote_deprecated(nonce, outdata, &outlen, &whitelist[scode_curr[vcpu->id]].utpm, tpmsel, tpmsel_len) != 0);

#if 0
	eu_trace("quote data len = %d!", outlen);
	eu_trace("quote data is: ");
	for(i=0;i<outlen;i++) {
		eu_trace("%x ", outdata[i]);
	}
	eu_trace("");
#endif

	/* copy output to guest */
	EU_CHKN( copy_to_current_guest(vcpu, out_addr, outdata, outlen));
    
	EU_CHKN( utpm_id_getpub(rsaModulus, &rsaLen));

	EU_CHK( rsaLen <= TPM_RSA_KEY_LEN);
    
	/* copy public key to guest */
	EU_CHKN( copy_to_current_guest(vcpu, out_addr + outlen, rsaModulus, TPM_RSA_KEY_LEN));
	outlen += TPM_RSA_KEY_LEN;

	/* copy out length to guest */
	EU_CHKN( copy_to_current_guest( vcpu, out_len_addr, &outlen, sizeof(outlen)));

	ret = 0;
 out:
	return ret;
}

u32 hc_utpm_quote(VCPU * vcpu, u32 nonce_addr, u32 tpmsel_addr, u32 sig_addr, u32 sig_len_addr,
                  u32 pcrComp_addr, u32 pcrCompLen_addr)
{
	uint8_t *sigdata=NULL;
	TPM_NONCE nonce;
	TPM_PCR_SELECTION tpmsel;
	u32 siglen, ret=1;
	uint8_t *pcrComp = NULL;
	uint32_t pcrCompLen = 0;

	eu_trace("********** uTPM Quote **********");
	eu_trace("nonce addr: %x, tpmsel addr: %x, sig_addr %x, sig_len_addr: %x!",
		 nonce_addr, tpmsel_addr, sig_addr, sig_len_addr);

	/* make sure that this vmmcall can only be executed when a PAL is running */
	EU_CHK( scode_curr[vcpu->id] != -1,
		eu_err_e("Quote ERROR: no PAL is running!"));

	/* get external nonce from guest */
	EU_CHKN( copy_from_current_guest(vcpu, &nonce, nonce_addr, sizeof(TPM_NONCE)));

	/* get TPM PCR selection from guest */
	/* FIXME: sizeof(TPM_PCR_SELECTION) may eventually change dynamically */
	EU_CHKN( copy_from_current_guest(vcpu, &tpmsel, tpmsel_addr, sizeof(TPM_PCR_SELECTION)));

	/* Get size of guest's sig buffer */
	EU_CHKN( copy_from_current_guest(vcpu, &siglen, sig_len_addr, sizeof(uint32_t)));
	eu_trace("Guest provided sig buffer of %d bytes", siglen);

	/* FIXME: This is just a rough sanity check that catches some uninitialized variables. */
	EU_CHK( siglen <= 5*TPM_QUOTE_SIZE,
		eu_err_e("ERROR: Guest-provided siglen value of %d seems ridiculous", siglen));

	/* Get size of guest's pcrComp buffer */
	EU_CHKN( copy_from_current_guest(vcpu, &pcrCompLen, pcrCompLen_addr, sizeof(uint32_t)));
	eu_trace("Guest provided pcrComp buffer of %d bytes", pcrCompLen);
    
	/**
	 * Allocate space to do internal processing
	 */
	EU_CHK( sigdata = malloc(siglen));
	EU_CHK( pcrComp = malloc(pcrCompLen));

    	/* FIXME: Still want to return a modified "siglen" in case the input buffer was too small.
	   I.e., this fails too aggressively. */
	EU_CHKN( ret = utpm_quote(&nonce, &tpmsel, sigdata, &siglen,
				  pcrComp, &pcrCompLen,
				  &whitelist[scode_curr[vcpu->id]].utpm));

	/* Some sanity-checking. TODO: replace with asserts & use tighter bound */
	if (siglen > 2*TPM_QUOTE_SIZE) {
		eu_err_e("ERROR: siglen (%d) > 2*TPM_QUOTE_SIZE", siglen);
		siglen = TPM_QUOTE_SIZE; /* FIXME: We should return some kind of error code */
		/* return 1; */ /* Don't return from here; it causes some kind of crash in the PAL */
	}
	
	eu_trace("quote sigdata len = %d!", siglen);
	//print_hex("  QD: ", sigdata, siglen);

	/* copy quote sig to guest */
	EU_CHKN( copy_to_current_guest(vcpu, sig_addr, sigdata, siglen));
	eu_trace("hc_utpm_quote: Survived copy_to_current_guest of %d bytes", siglen);

	/* copy pcrComp to guest */
	EU_CHKN( copy_to_current_guest(vcpu, pcrComp_addr, pcrComp, pcrCompLen));
	
	/* copy quote sig length to guest */
	EU_CHKN( copy_to_current_guest( vcpu, sig_len_addr, &siglen, sizeof(siglen)));
	eu_trace("hc_utpm_quote: Survived put_32bit_aligned_value_to_current_guest");

	ret=0;
 out:
	free(sigdata); sigdata = NULL;
	free(pcrComp); pcrComp = NULL;
	
	return ret;
}

uint32_t hc_utpm_utpm_id_getpub(VCPU * vcpu, gva_t dst_gva, gva_t dst_sz_gva)
{
	uint8_t *rsaModulus=NULL;
	uint32_t rv = 1;
	uint32_t dst_sz;

	eu_trace("********** uTPM id_getpub **********");

	/* make sure that this vmmcall can only be executed when a PAL is running */
	EU_CHK( scode_curr[vcpu->id] != -1,
		eu_err_e("ID_GETPUB ERROR: no PAL is running!"));

	EU_CHKN( copy_from_current_guest( vcpu, &dst_sz, dst_sz_gva, sizeof(dst_sz)));

	rsaModulus = malloc( dst_sz);
	EU_CHK( rsaModulus || (dst_sz == 0));

	EU_CHKN( rv = utpm_id_getpub(rsaModulus, &dst_sz));

	//print_hex("  N  : ", rsaModulus, TPM_RSA_KEY_LEN);
	EU_CHKN( copy_to_current_guest( vcpu, dst_gva, rsaModulus, dst_sz));
	EU_CHKN( copy_to_current_guest( vcpu, dst_sz_gva, &dst_sz, sizeof(dst_sz)));

	rv = 0;
 out:
	free(rsaModulus);
	return rv;
}

u32 hc_utpm_pcrread(VCPU * vcpu, u32 gvaddr, u32 num)
{
	TPM_DIGEST pcr;
	u32 rv = 1;

	eu_trace("********** uTPM pcrread **********");

	/* make sure that this vmmcall can only be executed when a PAL is running */
	EU_CHK( scode_curr[vcpu->id] != -1,
		eu_err_e("PCRRead ERROR: no PAL is running!"));

	/* make sure requested PCR number is in reasonable range */
	EU_CHK( num < TPM_PCR_NUM,
		eu_err_e("PCRRead ERROR: pcr num %d not correct!", num));

	/* read pcr value */
	EU_CHKN( rv = utpm_pcrread(&pcr, &whitelist[scode_curr[vcpu->id]].utpm, num));

	/* return pcr value to guest */
	EU_CHKN( copy_to_current_guest(vcpu, gvaddr, pcr.value, TPM_PCR_SIZE));

	rv = 0;
 out:
	return rv;
}


u32 hc_utpm_pcrextend(VCPU * vcpu, u32 idx, u32 meas_gvaddr)
{
	TPM_DIGEST measurement;
	u32 rv = 1;

	eu_trace("********** uTPM pcrextend **********");

	/* make sure that this vmmcall can only be executed when a PAL is running */
	EU_CHK( scode_curr[vcpu->id] != -1,
		eu_err_e("PCRExtend ERROR: no PAL is running!"));

	/* make sure requested PCR number is in reasonable range */
	EU_CHK( idx < TPM_PCR_NUM,
		eu_err_e("PCRExtend ERROR: pcr idx %d not correct!", idx));

	/* get data from guest */
	EU_CHKN( copy_from_current_guest(vcpu, (u8 *)measurement.value, meas_gvaddr, TPM_HASH_SIZE));

	/* extend pcr */
    //print_hex("PCRExtend data from guest: ", measurement.value, TPM_HASH_SIZE);    
	EU_CHKN( rv = utpm_extend(&measurement, &whitelist[scode_curr[vcpu->id]].utpm, idx));

	rv = 0;
 out:
	return rv;
}

u32 hc_utpm_rand(VCPU * vcpu, u32 buffer_addr, u32 numbytes_addr)
{
	u32 ret = 1;
	u8 buffer[MAX_TPM_RAND_DATA_LEN]; 
	u32 numbytes;

	/* make sure that this vmmcall can only be executed when a PAL is running */
	EU_CHK( scode_curr[vcpu->id] != -1,
		eu_err_e("PCRExtend ERROR: no PAL is running!"));

	// get the byte number requested
	EU_CHKN( copy_from_current_guest( vcpu, &numbytes, numbytes_addr, sizeof(numbytes)));
	EU_CHK( numbytes <= MAX_TPM_RAND_DATA_LEN,
		eu_err_e("GenRandom ERROR: requested rand data len %d too large!", numbytes));

	EU_CHKN( ret = utpm_rand(buffer, &numbytes),
		 eu_err_e("GenRandom ERROR: rand byte error; numbytes=%d!",
			  numbytes));

	/* copy random data to guest */
	EU_CHKN( copy_to_current_guest(vcpu, buffer_addr, buffer, numbytes));

	/* copy data length to guest */
	EU_CHKN( copy_to_current_guest( vcpu, numbytes_addr, &numbytes, sizeof(numbytes)));

	ret = 0;
 out:
	return ret;
}

/* Local Variables: */
/* mode:c           */
/* indent-tabs-mode:'t */
/* c-basic-offset:8 */
/* End:             */
