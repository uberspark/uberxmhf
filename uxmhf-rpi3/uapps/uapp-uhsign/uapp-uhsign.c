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
	uhsign hypapp
	guest hypercall to generate HMAC signature of data blob

        authors: matt mccormack (<matthew.mccormack@live.com>)
                amit vasudevan (<amitvasudevan@acm.org>)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <uart.h>
#include <debug.h>

#include <uhsign.h>
#include <hmac-sha1.h>
#include <xmhfcrypto.h>


//////
// access control via code white-listing
//////


// golden white-listing hash for libuhcall code
unsigned char whitelist_hash[] = {
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
bool uapp_uhsign_check_whitelist(uint32_t paddr, uint32_t size){
  hash_state md;
  int i;
  unsigned char computed_hash[HASH_SIZE];

  if ( sha1_memory((const unsigned char *)paddr, size, &computed_hash, HASH_SIZE) == CRYPT_OK ){
    #if 0
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
bool uapp_uhsign_va2pa(uint32_t va, u32 *pa){
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
void uapp_uhsign_checkacl(uint32_t va){
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
      if(uapp_uhsign_check_whitelist(paddr, WHITELIST_COMPARE_BYTES)){
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


__attribute__((section(".data"))) unsigned char uhsign_key[]="super_secret_key_for_hmac";
#define UHSIGN_KEY_SIZE (sizeof(uhsign_key))

bool uapp_uhsign_handlehcall(u32  uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len)
{
  uhsign_param_t *uhcp;

  if(uhcall_function != UAPP_UHSIGN_FUNCTION_SIGN)
    return false;

  uhcp=(uhsign_param_t *)uhcall_buffer;

  //debug dump
  #if 0
  _XDPRINTFSMP_("%s: elr_hyp va=0x%08x\n", __func__, sysreg_read_elrhyp());
  #endif

  //call acl function
  uapp_uhsign_checkacl(sysreg_read_elrhyp());

  //Call HMAC function
  unsigned long digest_size = HMAC_DIGEST_SIZE;
  unsigned char *digest_result;
  int i;

  if(hmac_sha1_memory(uhsign_key, (unsigned long) UHSIGN_KEY_SIZE, (unsigned char *) uhcp->pkt, (unsigned long) uhcp->pkt_size, digest_result, &digest_size)==CRYPT_OK) {
    for(i=0;i<digest_size;i++) {
      uhcp->digest[i]=(uint8_t)*(digest_result+i);
    }
    return true;
  } else {
    return false;
  }
}
