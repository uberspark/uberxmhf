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

#include <target.h>
#include <crypto_init.h>
#include <utpm.h>
#include <hc_utpm.h>
#include <scode.h> /* copy_from_guest */
#include <puttymem.h> /* vmalloc */
#include <sha1.h>

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
	uint32_t rv=0;

	TPM_PCR_INFO tpmPcrInfo;
	
	dprintf(LOG_TRACE, "\n[TV] ********** uTPM seal **********\n");
	dprintf(LOG_TRACE, "[TV] input_addr: %x, input_len %d, tpmPcrInfo_addr: %x, output_addr: %x!\n", input_addr, input_len, tpmPcrInfo_addr, output_addr);

	if(!vcpu || !input_addr || !tpmPcrInfo_addr || !output_addr || !output_len_addr) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: !vcpu || !input_addr || !tpmPcrInfo_addr || !output_addr || !output_len_addr\n");
		return 1;
	}

	/**
	 * check input data length
	 */
	/* include seal data header and possible AES encryption padding */
	if (input_len > (MAX_SEALDATA_LEN - SEALDATA_HEADER_LEN - 16) ) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: input data length is too large, lenth %#x\n", input_len);
		return 1;
	}

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: no PAL is running!\n");
		return 1;
	}

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* copy input data to host */
	copy_from_guest(vcpu, indata, input_addr, input_len);
	copy_from_guest(vcpu, (uint8_t*)&tpmPcrInfo, tpmPcrInfo_addr, sizeof(TPM_PCR_INFO));

	dprintf(LOG_TRACE, "[TV] input len = %d!\n", input_len);
	print_hex("  indata: ", indata, input_len);
	print_hex("  tpmPcrInfo: ", (uint8_t*)&tpmPcrInfo, sizeof(TPM_PCR_INFO));


	/* seal, verifying output is not too large */
	rv = utpm_seal(&whitelist[scode_curr[vcpu->id]].utpm,
								 &tpmPcrInfo,
								 indata, input_len,
								 output, &outlen,
								 g_hmackey, g_aeskey);
	if (rv != 0 || outlen > MAX_SEALDATA_LEN) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: output data length is too large, lenth %#x\n", outlen);
		return rv;
	}
	print_hex("  sealedData: ", output, outlen);

	/*copy output to guest */
	copy_to_guest(vcpu, output_addr, output, outlen);

	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(vcpu, output_len_addr, outlen);

	return rv;
}

uint32_t hc_utpm_unseal(VCPU * vcpu, uint32_t input_addr, uint32_t input_len,
											uint32_t output_addr, uint32_t output_len_addr,
											uint32_t digestAtCreation_addr)
{
	uint8_t indata[MAX_SEALDATA_LEN]; 
	uint8_t outdata[MAX_SEALDATA_LEN];
	uint32_t outlen;
	uint32_t ret;
	TPM_COMPOSITE_HASH digestAtCreation;

	dprintf(LOG_TRACE, "\n[TV:scode] ********** uTPM unseal **********\n");

	if(!vcpu || !input_addr || !output_addr || !output_len_addr || !digestAtCreation_addr) {
		dprintf(LOG_ERROR, "[TV:scode] Unseal ERROR: !vcpu || !input_addr || !output_addr || !output_len_addr || !digestAtCreation_addr\n");
		return 1;
	}
	
	dprintf(LOG_TRACE, "[TV:scode] input addr: %x, len %d, output addr: %x!\n",
					input_addr, input_len, output_addr);
	/* check input data length */
	if (input_len > MAX_SEALDATA_LEN) {
		dprintf(LOG_ERROR, "[TV:scode] Unseal ERROR: input data length is too large, lenth %#x\n", input_len);
		return 1;
	}

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV:scode] Seal ERROR: no PAL is running!\n");
		return 1;
	}

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* copy input data from guest */
	copy_from_guest(vcpu, indata, input_addr, input_len);

	print_hex("  [TV:scode] input data: ", indata, input_len);	

	/* unseal */
	if ((ret = utpm_unseal(&whitelist[scode_curr[vcpu->id]].utpm, indata, input_len,
												 outdata, &outlen, &digestAtCreation,
												 g_hmackey, g_aeskey))) {
		dprintf(LOG_ERROR, "[TV:scode] Unseal ERROR: utpm_unseal fail!\n");
		return 1;
	}

	print_hex("  [TV:scode] output (unsealed) data: ", outdata, outlen);	

	/* check output data length */
	if (outlen > MAX_SEALDATA_LEN ) {
		dprintf(LOG_ERROR, "[TV:scode] Unseal ERROR: output data length is too large, lenth %#x\n", outlen);
		return 1;
	}

	/* copy output to guest */
	copy_to_guest(vcpu, output_addr, outdata, outlen);
	copy_to_guest(vcpu, digestAtCreation_addr, (uint8_t*)&digestAtCreation, TPM_HASH_SIZE);
	
	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(vcpu, output_len_addr, outlen);
	return 0;
}


u32 hc_utpm_seal_deprecated(VCPU * vcpu, u32 input_addr, u32 input_len, u32 pcrAtRelease_addr, u32 output_addr, u32 output_len_addr)
{
	unsigned int i;
	u32 outlen;
	u8 pcr[TPM_PCR_SIZE];
	u8 indata[MAX_SEALDATA_LEN];  
	u8 output[MAX_SEALDATA_LEN]; 

	dprintf(LOG_TRACE, "\n[TV] ********** uTPM seal DEPRECATED **********\n");
	dprintf(LOG_TRACE, "[TV] input addr: %x, len %d, pcr addr: %x, output addr: %x!\n", input_addr, input_len, pcrAtRelease_addr, output_addr);
	/* check input data length */
	/* include seal data header and possible AES encryption padding */
	if (input_len > (MAX_SEALDATA_LEN-SEALDATA_HEADER_LEN - 16) ) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: input data length is too large, lenth %#x\n", input_len);
		return 1;
	}

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: no PAL is running!\n");
		return 1;
	}

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* copy input data to host */
	copy_from_guest(vcpu, indata, input_addr, input_len);

#if 0
	dprintf(LOG_TRACE, "[TV] input len = %d!\n", input_len);
	dprintf(LOG_TRACE, "[TV] input data is:");
	for(i=0;i<input_len;i++) {
		dprintf(LOG_TRACE, "%x ", indata[i]);
	}
	dprintf(LOG_TRACE, "[TV] \n");
#endif

	if (pcrAtRelease_addr != 0) {
		/* seal data to other PAL */
		/* copy pcr value at release to host */
		copy_from_guest(vcpu, pcr, pcrAtRelease_addr, TPM_PCR_SIZE);
	} else {
		/* seal data to our own */
		/* use current PAL's PCR value */
		dprintf(LOG_TRACE, "[TV] get pcr from current PAL's softTPM!\n");
		vmemcpy(pcr, whitelist[scode_curr[vcpu->id]].utpm.pcr_bank, TPM_PCR_SIZE);
	}

#if 1
	dprintf(LOG_TRACE, "[TV] pcr value is:");
	for(i=0;i<TPM_PCR_SIZE;i++) {
		dprintf(LOG_TRACE, "%x ", pcr[i]);
	}
	dprintf(LOG_TRACE, "\n");
#endif

	/* seal */
	utpm_seal_deprecated(pcr, indata, input_len, output, &outlen, g_hmackey, g_aeskey);

#if 1
	dprintf(LOG_TRACE, "[TV] sealed data len = %d!\n", outlen);
	dprintf(LOG_TRACE, "[TV] sealed data is: ");
	for(i=0;i<outlen;i++) {
		dprintf(LOG_TRACE, "%x ", output[i]);
	}
	dprintf(LOG_TRACE, "\n");
#endif

	/* check output data length */
	if (outlen > MAX_SEALDATA_LEN) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: output data length is too large, lenth %#x\n", outlen);
		return 1;
	}

	/*copy output to guest */
	copy_to_guest(vcpu, output_addr, output, outlen);

	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(vcpu, output_len_addr, outlen);

	return 0;
}

u32 hc_utpm_unseal_deprecated(VCPU * vcpu, u32 input_addr, u32 input_len, u32 output_addr, u32 output_len_addr)
{
	unsigned int i;
	u8 indata[MAX_SEALDATA_LEN]; 
	u8 outdata[MAX_SEALDATA_LEN];
	u32 outlen;
	u32 ret;

	dprintf(LOG_TRACE, "\n[TV] ********** uTPM unseal DEPRECATED **********\n");
	dprintf(LOG_TRACE, "[TV] input addr: %x, len %d, output addr: %x!\n", input_addr, input_len, output_addr);
	/* check input data length */
	if (input_len > MAX_SEALDATA_LEN) {
		dprintf(LOG_ERROR, "[TV] Unseal ERROR: input data length is too large, lenth %#x\n", input_len);
		return 1;
	}

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: no PAL is running!\n");
		return 1;
	}

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* copy input data from guest */
	copy_from_guest(vcpu, indata, input_addr, input_len);

#if 0
	dprintf(LOG_TRACE, "[TV] input len = %d!\n", input_len);
	dprintf(LOG_TRACE, "[TV] input data is:");
	for(i=0;i<input_len;i++) {
		dprintf(LOG_TRACE, "%x ", indata[i]);
	}
	dprintf(LOG_TRACE, "[TV] \n");
#endif

	/* unseal */
	if ((ret = utpm_unseal_deprecated(&whitelist[scode_curr[vcpu->id]].utpm, indata, input_len, outdata, &outlen, g_hmackey, g_aeskey))) {
		dprintf(LOG_ERROR, "[TV] Unseal ERROR: utpm_unseal fail!\n");
		return 1;
	}

#if 1
	dprintf(LOG_TRACE, "[TV] unsealed data len = %d!\n", outlen);
	dprintf(LOG_TRACE, "[TV] unsealed data is: ");
	for(i=0;i<outlen;i++) {
		dprintf(LOG_TRACE, "%x ", outdata[i]);
	}
	dprintf(LOG_TRACE, "\n");
#endif

	/* check output data length */
	if (outlen > MAX_SEALDATA_LEN ) {
		dprintf(LOG_ERROR, "[TV] Seal ERROR: output data length is too large, lenth %#x\n", outlen);
		return 1;
	}

	/* copy output to guest */
	copy_to_guest(vcpu, output_addr, outdata, outlen);

	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(vcpu, output_len_addr, outlen);
	return 0;
}

u32 hc_utpm_quote_deprecated(VCPU * vcpu, u32 nonce_addr, u32 tpmsel_addr, u32 out_addr, u32 out_len_addr)
{
	u8 outdata[TPM_QUOTE_SIZE];
	u8 nonce[TPM_NONCE_SIZE];
	u8 tpmsel[MAX_PCR_SEL_SIZE];
	u32 outlen, ret;
	u32 i, num;
	u32 tpmsel_len;

	dprintf(LOG_TRACE, "\n[TV] ********** uTPM Quote [DEPRECATED] **********\n");
	dprintf(LOG_TRACE, "[TV] nonce addr: %x, tpmsel addr: %x, output addr %x, outlen addr: %x!\n", nonce_addr, tpmsel_addr, out_addr, out_len_addr);
	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] Quote ERROR: no PAL is running!\n");
		return 1;
	}	

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* get TPM PCR selection from guest */
	num = get_32bit_aligned_value_from_guest(vcpu, tpmsel_addr);
	if (num > MAX_PCR_SEL_NUM) {
		dprintf(LOG_ERROR, "[TV] Quote ERROR: select too many PCR!\n");
		return 1;
	}
	tpmsel_len = 4+4*num;
	dprintf(LOG_TRACE, "[TV] %d pcrs are selected!\n", num);

	copy_from_guest(vcpu, tpmsel, tpmsel_addr, tpmsel_len);
	for( i=0 ; i< num ; i++ )  {
		if (*(((u32 *)(tpmsel+4))+i) >= TPM_PCR_NUM) {
			dprintf(LOG_ERROR, "[TV] Quote ERROR: bad format of TPM PCR num!\n");
			return 1;
		}
	}

	/* get external nonce from guest */
	copy_from_guest(vcpu, nonce, nonce_addr, TPM_NONCE_SIZE);

#if 1
	dprintf(LOG_TRACE, "[TV] external nonce is: ");
	for(i=0;i<TPM_NONCE_SIZE;i++) {
		dprintf(LOG_TRACE, "%x ", nonce[i]);
	}
	dprintf(LOG_TRACE, "\n");
#endif

	if ((ret = utpm_quote_deprecated(nonce, outdata, &outlen, &whitelist[scode_curr[vcpu->id]].utpm, tpmsel, tpmsel_len, (u8 *)(&g_rsa))) != 0) {
		dprintf(LOG_ERROR, "[TV] quote ERROR: utpm_quote fail!\n");
		return 1;
	}

#if 0
	dprintf(LOG_TRACE, "[TV] quote data len = %d!\n", outlen);
	dprintf(LOG_TRACE, "[TV] quote data is: ");
	for(i=0;i<outlen;i++) {
		dprintf(LOG_TRACE, "%x ", outdata[i]);
	}
	dprintf(LOG_TRACE, "\n");
#endif

	/* copy output to guest */
	copy_to_guest(vcpu, out_addr, outdata, outlen);

	/* copy public key to guest */
	copy_to_guest(vcpu, out_addr + outlen, (u8 *)(g_rsa.N.p), TPM_RSA_KEY_LEN);
	outlen += TPM_RSA_KEY_LEN;

	/* copy out length to guest */
	put_32bit_aligned_value_to_guest(vcpu, out_len_addr, outlen);
	return 0;
}

u32 hc_utpm_quote(VCPU * vcpu, u32 nonce_addr, u32 tpmsel_addr, u32 sig_addr, u32 sig_len_addr,
                  u32 pcrComp_addr, u32 pcrCompLen_addr)
{
    uint8_t *sigdata=NULL;
	TPM_NONCE nonce;
	TPM_PCR_SELECTION tpmsel;
	u32 siglen, ret=0;
    uint8_t *pcrComp = NULL;
    uint32_t pcrCompLen = 0;

	dprintf(LOG_TRACE, "\n[TV] ********** uTPM Quote **********\n");
	dprintf(LOG_TRACE, "[TV] nonce addr: %x, tpmsel addr: %x, sig_addr %x, sig_len_addr: %x!\n",
					nonce_addr, tpmsel_addr, sig_addr, sig_len_addr);

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] Quote ERROR: no PAL is running!\n");
		ret = 1;
		goto out;
	}	

	/* XXX FIXME: check input data and output data are all in PAL's memory range */

	/* get external nonce from guest */
	copy_from_guest(vcpu, (void*)&nonce, nonce_addr, sizeof(TPM_NONCE));

	/* get TPM PCR selection from guest */
	/* FIXME: sizeof(TPM_PCR_SELECTION) may eventually change dynamically */
	copy_from_guest(vcpu, (void*)&tpmsel, tpmsel_addr, sizeof(TPM_PCR_SELECTION));

	/* Get size of guest's sig buffer */
	copy_from_guest(vcpu, (void*)&siglen, sig_len_addr, sizeof(uint32_t));
	dprintf(LOG_TRACE, "[TV] Guest provided sig buffer of %d bytes\n", siglen);

	/* FIXME: This is just a rough sanity check that catches some uninitialized variables. */
	if(siglen > 5*TPM_QUOTE_SIZE) {
			dprintf(LOG_ERROR, "[TV] ERROR: Guest-provided siglen value of %d seems ridiculous\n", siglen);
			ret = 1;
			goto out;
	}

    /* Get size of guest's pcrComp buffer */
	copy_from_guest(vcpu, (void*)&pcrCompLen, pcrCompLen_addr, sizeof(uint32_t));
	dprintf(LOG_TRACE, "[TV] Guest provided pcrComp buffer of %d bytes\n", pcrCompLen);
    
	/**
	 * Allocate space to do internal processing
	 */
	if(NULL == (sigdata = vmalloc(siglen))) {
			dprintf(LOG_ERROR, "[TV] ERROR: vmalloc(%d) failed!\n", siglen);
			ret = 1;
			goto out;
	}

    if(NULL == (pcrComp = vmalloc(pcrCompLen))) {
			dprintf(LOG_ERROR, "[TV] ERROR: vmalloc(%d) failed!\n", siglen);
			ret = 1;
			goto out;
    }

    
	/* FIXME: Still want to return a modified "siglen" in case the input buffer was too small.
	   I.e., this fails too aggressively. */
	if ((ret = utpm_quote(&nonce, &tpmsel, sigdata, &siglen,
                          pcrComp, &pcrCompLen,
                          &whitelist[scode_curr[vcpu->id]].utpm,
                          (u8 *)(&g_rsa))) != 0) {
		dprintf(LOG_ERROR, "[TV] ERROR: utpm_quote failed!\n");
		return 1;
	}

	/* Some sanity-checking. TODO: replace with asserts & use tighter bound */
	if(siglen > 2*TPM_QUOTE_SIZE) {
			dprintf(LOG_ERROR, "[TV] ERROR: siglen (%d) > 2*TPM_QUOTE_SIZE\n", siglen);
			siglen = TPM_QUOTE_SIZE; /* FIXME: We should return some kind of error code */
			/* return 1; */ /* Don't return from here; it causes some kind of crash in the PAL */
	}
	
	dprintf(LOG_TRACE, "[TV] quote sigdata len = %d!\n", siglen);
	//print_hex("  QD: ", sigdata, siglen);

	/* copy quote sig to guest */
	copy_to_guest(vcpu, sig_addr, sigdata, siglen);

    /* copy pcrComp to guest */
	copy_to_guest(vcpu, pcrComp_addr, pcrComp, pcrCompLen);
    
    
	dprintf(LOG_TRACE, "[TV] hc_utpm_quote: Survived copy_to_guest of %d bytes\n", siglen);
	
	/* copy quote sig length to guest */
	put_32bit_aligned_value_to_guest(vcpu, sig_len_addr, siglen);
	dprintf(LOG_TRACE, "[TV] hc_utpm_quote: Survived put_32bit_aligned_value_to_guest\n");

	out:

	if(sigdata) { vfree(sigdata); sigdata = NULL; }
	
	return ret;
}

uint32_t hc_utpm_utpm_id_getpub(VCPU * vcpu, uint32_t gvaddr)
{
  uint8_t rsaModulus[TPM_RSA_KEY_LEN];
	dprintf(LOG_TRACE, "\n[TV] ********** uTPM id_getpub **********\n");

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] ID_GETPUB ERROR: no PAL is running!\n");
		return 1;
	}

	/* Must use MPI export function to get big endian N */
	if(mpi_write_binary(&g_rsa.N, rsaModulus, TPM_RSA_KEY_LEN) != 0) {
			dprintf(LOG_ERROR, "mpi_write_binary ERROR\n");
			return 1;
	}

	//print_hex("  N  : ", rsaModulus, TPM_RSA_KEY_LEN);
	
	/* XXX TODO FIXME: RSA public identity key should be part of uTPM
	 * structure and not a global variable here in scode.c */
	copy_to_guest(vcpu, gvaddr, rsaModulus, TPM_RSA_KEY_LEN);
	
	return 0;
}

u32 hc_utpm_pcrread(VCPU * vcpu, u32 gvaddr, u32 num)
{
	TPM_DIGEST pcr;

	dprintf(LOG_TRACE, "\n[TV] ********** uTPM pcrread **********\n");

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] PCRRead ERROR: no PAL is running!\n");
		return 1;
	}

	/* make sure requested PCR number is in reasonable range */
	if (num >= TPM_PCR_NUM)
	{
		dprintf(LOG_ERROR, "[TV] PCRRead ERROR: pcr num %d not correct!\n", num);
		return 1;
	}

	/* read pcr value */
	utpm_pcrread(&pcr, &whitelist[scode_curr[vcpu->id]].utpm, num);

	/* return pcr value to guest */
	copy_to_guest(vcpu, gvaddr, pcr.value, TPM_PCR_SIZE);

	return 0;
}


u32 hc_utpm_pcrextend(VCPU * vcpu, u32 gvaddr, u32 len, u32 num)
{
	u8 data[MAX_TPM_EXTEND_DATA_LEN]; 
	TPM_DIGEST hash;

	dprintf(LOG_TRACE, "\n[TV] ********** uTPM pcrextend **********\n");

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] PCRExtend ERROR: no PAL is running!\n");
		return 1;
	}

	/* make sure requested PCR number is in reasonable range */
	if (num >= TPM_PCR_NUM)
	{
		dprintf(LOG_ERROR, "[TV] PCRExtend ERROR: pcr num %d not correct!\n", num);
		return 1;
	}

	/* make sure the extended data is not too big */
	if (len > MAX_TPM_EXTEND_DATA_LEN)
	{
		dprintf(LOG_ERROR, "[TV] PCRExtend ERROR: extend data len %d not correct!\n", len);
		return 1;
	}

	/* get data from guest */
	copy_from_guest(vcpu, (u8 *)data, gvaddr, len);

	/* hash input data */
	sha1_buffer((unsigned char*)data, len, hash.value);

	/* extend pcr */
	utpm_extend(&hash, &whitelist[scode_curr[vcpu->id]].utpm, num);

	return 0;
}

u32 hc_utpm_rand(VCPU * vcpu, u32 buffer_addr, u32 numbytes_addr)
{
	u32 ret;
	u8 buffer[MAX_TPM_RAND_DATA_LEN]; 
	u32 numbytes;

	/* make sure that this vmmcall can only be executed when a PAL is running */
	if (scode_curr[vcpu->id]== -1) {
		dprintf(LOG_ERROR, "[TV] GenRandom ERROR: no PAL is running!\n");
		return 1;
	}

	// get the byte number requested
	numbytes = get_32bit_aligned_value_from_guest(vcpu, numbytes_addr);
	if (numbytes > MAX_TPM_RAND_DATA_LEN)
	{
		dprintf(LOG_ERROR, "[TV] GenRandom ERROR: requested rand data len %d too large!\n", numbytes);
		return 1;
	}

	ret = utpm_rand(buffer, &numbytes);
	if (ret != UTPM_SUCCESS) {
		dprintf(LOG_ERROR, "[TV] GenRandom ERROR: rand byte error; numbytes=%d!",
						numbytes);
		return 1;
	}

	/* copy random data to guest */
	copy_to_guest(vcpu, buffer_addr, buffer, numbytes);

	/* copy data length to guest */
	put_32bit_aligned_value_to_guest(vcpu, numbytes_addr, numbytes);

	return 0;
}
