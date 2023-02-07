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
	pa5encfs hypapp
	FUSE encrypted filesystem hypapp

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <uart.h>
#include <debug.h>

#include <xmhfcrypto.h>
#include <aes.h>
#include <pa5encfs.h>

/*
	do_crypt using libxmhfcrypto aes primitive
	aeskey of size TPM_AES_KEY_LEN_BYTES (16)
	iv of size TPM_AES_KEY_LEN_BYTES (16) which is random
	cbc_start
	cbc_encrypt
	cbc_done
 */
__attribute__((section(".data"))) uint8_t pa5encfs_aes_iv[AES_KEY_LEN_BYTES] =
	{
			0x1a, 0x2a, 0x3a, 0x4a, 0x5a, 0x6a, 0x7a, 0x8a,
			0x1b, 0x2b, 0x3b, 0x4b, 0x5b, 0x6b, 0x7b, 0x8b
	};
__attribute__((section(".data"))) uint8_t pa5encfs_aes_key[AES_KEY_LEN_BYTES] =
	{
			0xfa, 0xea, 0xda, 0xca, 0xba, 0xaa, 0x9a, 0x8a,
			0xfb, 0xeb, 0xdb, 0xcb, 0xbb, 0xab, 0x9b, 0x8b
	};

__attribute__((section(".data"))) symmetric_CBC cbc_ctx;


//return true if handled the hypercall, false if not
bool uapp_pa5encfs_handlehcall(u32 uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len){
	pa5encfs_param_t *ep;

	ep = (pa5encfs_param_t *)uhcall_buffer;

	if(uhcall_function == UAPP_PA5ENCFS_FUNCTION_START){

		/* Init Engine */
		if( rijndael_cbc_start(pa5encfs_aes_iv, pa5encfs_aes_key, AES_KEY_LEN_BYTES, 0, &cbc_ctx) != CRYPT_OK )
			ep->result = 0;
		else
			ep->result = 1;

		return true;

	}else if (uhcall_function == UAPP_PA5ENCFS_FUNCTION_ENCRYPT){

		if( rijndael_cbc_encrypt(ep->inbuf, ep->outbuf, ep->inlen, &cbc_ctx) != CRYPT_OK)
			ep->result=0;
		else
			ep->result=1;

		return true;

	}else if (uhcall_function == UAPP_PA5ENCFS_FUNCTION_DECRYPT){

	    if( rijndael_cbc_decrypt(ep->inbuf, ep->outbuf, ep->inlen, &cbc_ctx) != CRYPT_OK)
	    	ep->result=0;
		else
			ep->result=1;


		return true;

	}else if (uhcall_function == UAPP_PA5ENCFS_FUNCTION_DONE){

		if( rijndael_cbc_done( &cbc_ctx) != CRYPT_OK)
	    	ep->result=0;
		else
			ep->result=1;

		return true;

	}else{

		return false;
	}

}
