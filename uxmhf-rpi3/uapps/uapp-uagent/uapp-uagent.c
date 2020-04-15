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
 * Authors: Matt McCormack (<matthew.mccormack@live.com>)
 *          Amit Vasudevan (<amitvasudevan@acm.org>)
 */

/*
	uagent hypapp
	guest hypercall to encrypt/decrypt a data blob

        authors: matt mccormack (<matthew.mccormack@live.com>)
                amit vasudevan (<amitvasudevan@acm.org>)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <uart.h>
#include <debug.h>

#include <uagent.h>
#include <aes.h>
#include <hmac-sha1.h>
#include <xmhfcrypto.h>


//////
// access control via code white-listing
//////


// golden white-listing hash for libuhcall code
uint8_t whitelist_hash[] = {
        0x8f, 0xd1, 0x2d, 0x2a, 0xb8, 
        0x68, 0x0f, 0x67, 0x1f, 0x81,
        0xc8, 0xe3, 0x47, 0x69, 0x7d, 
        0x86, 0x05, 0x4d, 0xd9, 0xfd
};
#define HASH_SIZE (sizeof(whitelist_hash)/sizeof(unsigned char))
#define WHITELIST_COMPARE_BYTES 32


//check white-listing hash with a memory regions specified by
//physical address and size
//return: true if ok, false if not
bool uapp_uagent_check_whitelist(uint32_t paddr, uint32_t size){
  uint8_t computed_hash[HASH_SIZE];

  if(sha1_memory((const uint8_t *)paddr, size, &computed_hash, HASH_SIZE) == CRYPT_OK){
    #if 0
    uint32_t i;    
     _XDPRINTFSMP_("Hash follows:\n\n");
    for (i=0; i < HASH_SIZE; i++)
      _XDPRINTFSMP_("0x%02x ", computed_hash[i]);
     _XDPRINTFSMP_("\n\n");
    #endif
    if (memcmp (computed_hash, whitelist_hash, HASH_SIZE) != 0) {
      //hash did not match
      return false;
    }else{
      //hash matched
      return true;
    }

  }else{
    //sha1_memory barfed, so just return false
    return false;
  }
}

// translate virtual address to physical address
bool uapp_uagent_va2pa(uint32_t va, u32 *pa){
	u32 par;

	sysreg_ats1cpr(va);
	par = sysreg_read_par();

	if(par & 0x1)
		return false; 	

	par &= 0xFFFFF000UL;

	*pa = par;
	return true;
}

// main function to perform access control of signing facility
// acl is based on code white-list hashing
void uapp_uagent_checkacl(uint32_t va){
    u32 paddr;
    
    #if 0
    _XDPRINTFSMP_("%s: enter\n", __func__);
    #endif

    if(!va2pa((uint32_t)va, &paddr)){
      #if 0
      _XDPRINTFSMP_("%s: no va to pa mapping for 0\n", __func__);
      #endif
      //__SECURITY ACTION__: no va to pa mapping in guest; fail silently for now
    }else{
      #if 0
      _XDPRINTFSMP_("va to pa mapping=0x%08x\n", __func__, paddr);
      #endif
      if(uapp_uagent_check_whitelist(paddr, WHITELIST_COMPARE_BYTES)){
          //_XDPRINTFSMP_("ACL passed\n");
          //acl passed
      }else{
         //__SECURITY ACTION__: acl check error; fail silently for now
      }
    }
    #if 0
    _XDPRINTFSMP_("%s: exit\n", __func__);
    #endif
}

#define BLOCK_SIZE 16

uint32_t calc_crypto_size(uint32_t input_size){
  uint32_t num_blocks;
  num_blocks=input_size/BLOCK_SIZE;
  if(input_size%BLOCK_SIZE)
    num_blocks++;
  return num_blocks*BLOCK_SIZE;
}
 
__attribute__((section(".data"))) uint8_t uagent_key[16]={
  0x73, 0x75, 0x70, 0x65, 0x72, 0x5f, 0x73, 0x65, 0x63, 0x72, 0x65,
  0x74, 0x5f, 0x6b, 0x65, 0x79
}; //"super_secret_key"
__attribute__((section(".data"))) uint8_t iv[16]={
  0x31, 0x32, 0x33, 0x34, 0x035, 0x36, 0x37, 0x38, 0x39, 0x30, 0x31,
  0x32, 0x33, 0x34, 0x35, 0x36
}; //"1234567890123456"
#define UAGENT_KEY_SIZE (sizeof(uagent_key))

bool uapp_uagent_handlehcall(u32  uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len)
{
  uagent_param_t *uhcp;

  if(uhcall_function != UAPP_UAGENT_FUNCTION_SIGN)
    return false;

  uhcp=(uagent_param_t *)uhcall_buffer;

  //debug dump
  #if 0
  _XDPRINTFSMP_("%s: elr_hyp va=0x%08x\n", __func__, sysreg_read_elrhyp());
  #endif

  //call acl function
  //uapp_uagent_checkacl(sysreg_read_elrhyp());

  //Call AES_CBC function(s)
  symmetric_CBC cbc_ctx;
  uint8_t data_buffer[1600];

  memset(data_buffer, 0, 1600);

  if(rijndael_cbc_start(iv, uagent_key, UAGENT_KEY_SIZE, 0, &cbc_ctx)) {
    return false;
  }
  
  uint32_t cipher_len=calc_crypto_size(uhcp->pkt_size);

  // encrypt
  if(uhcp->op==1){
    if(rijndael_cbc_encrypt(uhcp->pkt_data, data_buffer, (unsigned long) cipher_len, &cbc_ctx)) {
      return false;
    }
    memset(uhcp->pkt_data, 0, 1600);
    memcpy(uhcp->pkt_data, data_buffer, cipher_len);
    rijndael_cbc_done(&cbc_ctx);
    return true;
    //decrypt
  } else if(uhcp->op==2){
    if(rijndael_cbc_decrypt(uhcp->pkt_data, data_buffer, (unsigned long) cipher_len, &cbc_ctx)) {
      return false;
    }
    memset(uhcp->pkt_data, 0, 1600);
    memcpy(uhcp->pkt_data, data_buffer, cipher_len);
    rijndael_cbc_done(&cbc_ctx);
    return true;
  } else {
    return false;
  }
}
