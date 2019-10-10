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
 * Author: Matt McCormack (matthew.mccormack@live.com)
 *
 */

/*
	uhsign hypapp
	guest hypercall to generate HMAC signature of data blob

        authors: matt mccormack (mmccorm1@andrew.cmu.edu)
                amit vasudevan (<amitvasudevan@acm.org>)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

#include <uhsign.h>
#include <hmac-sha1.h>
#include <xmhfcrypto.h>


//////
// access control via code white-listing
//////


// test white-listing hash
unsigned char whitelist_hash[] = {
        0xa9, 0x99, 0x3e, 0x36, 0x47, 
        0x06, 0x81, 0x6a, 0xba, 0x3e, 
        0x25, 0x71, 0x78, 0x50, 0xc2, 
        0x6c, 0x9c, 0xd0, 0xd8, 0x9d 
};

#define HASH_SIZE (sizeof(whitelist_hash)/sizeof(unsigned char))

//check white-listing hash with a memory regions specified by
//physical address and size
//return: true if ok, false if not
bool uapp_uhsign_check_whitelist(uint32_t paddr, uint32_t size){
  hash_state md;
  unsigned char computed_hash[HASH_SIZE];

  if ( sha1_memory((const unsigned char *)paddr, size, &compute_hash, HASH_SIZE) == CRYPT_OK ){
    return true;
  }else{
    return false;
  }
}




// translate virtual address to physical address
bool uapp_uhsign_va2pa(uint32_t va, u32 *pa){
	u32 par;

	sysreg_ats1cpr(va);
	par = sysreg_read_par();

	if(par & 0x1)
		return false; 	//_XDPRINTFSMP_("%s: Fault in address translation. Halting!\n", __func__);

	par &= 0xFFFFF000UL;

	*pa = par;
	return true;
}

void uapp_uhsign_checkacl(uint32_t va){
    u32 paddr;
    _XDPRINTFSMP_("%s: enter\n", __func__);

	  if(!va2pa((uint32_t)va, &paddr)){
      _XDPRINTFSMP_("%s: no va to pa mapping for 0\n", __func__);
    }else{
      _XDPRINTFSMP_("va to pa mapping=0x%08x\n", __func__, paddr);
    }

    _XDPRINTFSMP_("%s: exit\n", __func__);

}






//////








__attribute__((section(".data"))) unsigned char key[]="super_secret_key_for_hmac";
#define KEY_SIZE (sizeof(key))

bool uapp_uhsign_handlehcall(u32  uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len)
{
  uhsign_param_t *uhcp;

  if(uhcall_function != UAPP_UHSIGN_FUNCTION_SIGN)
    return false;
  uhcp=(uhsign_param_t *)uhcall_buffer;

  //debug dump
  _XDPRINTFSMP_("%s: va=0x%08x, pa=0x%08x\n", __func__, uhcp->vaddr, (uint32_t)uhcp);
  
  //call acl function
  uapp_uhsign_checkacl(uhcp->vaddr);


  //Call HMAC function
  unsigned long digest_size = HMAC_DIGEST_SIZE;
  unsigned char *digest_result;
  int i;
  if(hmac_sha1_memory(key, (unsigned long) KEY_SIZE, (unsigned char *) uhcp->pkt, (unsigned long) uhcp->pkt_size, digest_result, &digest_size)==CRYPT_OK) {
    for(i=0;i<digest_size;i++) {
      uhcp->digest[i]=(uint8_t)*(digest_result+i);
    }
    _XDPRINTFSMP_("%s: hmac successful!\n", __func__);
    return true;
  } else {
    _XDPRINTFSMP_("%s: hmac error!\n", __func__);
    return false;
  }

}

  
