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

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>


#include <uberspark/uobjrtl/crypto/include/ciphers/aes/aes.h>
#include <uberspark/uobjrtl/crypto/include/mac/hmacsha1/hmacsha1.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/whitelist.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uagent.h>



#define UAGENT_BLOCK_SIZE 16

uint32_t calc_crypto_size(uint32_t input_size){
  uint32_t num_blocks;
  num_blocks=input_size/UAGENT_BLOCK_SIZE;
  if(input_size%UAGENT_BLOCK_SIZE)
    num_blocks++;
  return num_blocks*UAGENT_BLOCK_SIZE;
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
  _XDPRINTFSMP_("%s: elr_hyp va=0x%08x\n", __func__, CASM_FUNCCALL(sysreg_read_elrhyp, CASM_NOPARAM));
  #endif

  //call acl function
  uapp_checkacl(CASM_FUNCCALL(sysreg_read_elrhyp, CASM_NOPARAM));

  //Call AES_CBC function(s)
  symmetric_CBC cbc_ctx;
  uint8_t data_buffer[1600];

  uberspark_uobjrtl_crt__memset(data_buffer, 0, 1600);

  if(uberspark_uobjrtl_crypto__ciphers_aes__rijndael_cbc_start(iv, uagent_key, UAGENT_KEY_SIZE, 0, &cbc_ctx)) {
    return false;
  }
  
  uint32_t cipher_len=calc_crypto_size(uhcp->pkt_size);

  // encrypt
  if(uhcp->op==1){
    if(uberspark_uobjrtl_crypto__ciphers_aes__rijndael_cbc_encrypt(uhcp->pkt_data, data_buffer, (unsigned long) cipher_len, &cbc_ctx)) {
      return false;
    }
    uberspark_uobjrtl_crt__memset(uhcp->pkt_data, 0, 1600);
    uberspark_uobjrtl_crt__memcpy(uhcp->pkt_data, data_buffer, cipher_len);
    uberspark_uobjrtl_crypto__ciphers_aes__rijndael_cbc_done(&cbc_ctx);
    return true;
    //decrypt
  } else if(uhcp->op==2){
    if(uberspark_uobjrtl_crypto__ciphers_aes__rijndael_cbc_decrypt(uhcp->pkt_data, data_buffer, (unsigned long) cipher_len, &cbc_ctx)) {
      return false;
    }
    uberspark_uobjrtl_crt__memset(uhcp->pkt_data, 0, 1600);
    uberspark_uobjrtl_crt__memcpy(uhcp->pkt_data, data_buffer, cipher_len);
    uberspark_uobjrtl_crypto__ciphers_aes__rijndael_cbc_done(&cbc_ctx);
    return true;
  } else {
    return false;
  }
}
