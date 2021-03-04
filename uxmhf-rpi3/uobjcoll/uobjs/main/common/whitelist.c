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
 *         Matt McCormack (matthew.mccormack@live.com)
 *
 */

/*
        code whitelisting (acl check for code calling uapps)

	author: amit vasudevan (amitvasudevan@acm.org)
                matt mccormack (matthew.mccormack@live.com)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/pl011uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>

//#include <uberspark/uobjrtl/crypto/include/basedefs.h>
#include <uberspark/uobjrtl/crypto/include/mac/hmacsha1/hmacsha1.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/whitelist.h>


// golden white-listing hash for libuhcall code
uint8_t whitelist_hash[] = {
  0x8f, 0xd1, 0x2d, 0x2a, 0xb8, 0x68, 0x0f, 0x67, 0x1f, 0x81,
  0xc8, 0xe3, 0x47, 0x69, 0x7d, 0x86, 0x05, 0x4d, 0xd9, 0xfd
};

#define WHITELIST_HASH_SIZE (sizeof(whitelist_hash)/sizeof(uint8_t))
#define WHITELIST_COMPARE_BYTES 32

/* check white-listing hash with a memory regions specified by
 * physical address and size
 * return: true if ok, false if no
 */
bool uapp_check_whitelist(uint32_t paddr, uint32_t size){
  uint8_t computed_hash[WHITELIST_HASH_SIZE];
  unsigned long hash_size=WHITELIST_HASH_SIZE;

  if(uberspark_uobjrtl_crypto__hashes_sha1__sha1_memory((const unsigned char *)paddr, size, &computed_hash, &hash_size) == CRYPT_OK){

    // debug printout of hash
    #if 0
    int i;
    _XDPRINTFSMP_("Hash follows: \n\n");
    for(i=0; i<WHITELIST_HASH_SIZE; i++)
      _XDPRINTFSMP_("0x%02x ", computed_hash[i]);
    _XDPRINTFSMP_("\n\n");
    #endif

    if(uberspark_uobjrtl_crt__memcmp(computed_hash, whitelist_hash, WHITELIST_HASH_SIZE) != 0){
      // hash did not match
      return false;
    }else{
      // hash matched
      return true;
    }

  }else{
    // sha1_memory barfed, so just return false
    return false;
  }
}

/* translate virtual address to physical address */
bool uapp_va2pa(uint32_t va, u32 *pa){
  u32 par;
  
  sysreg_ats1cpr(va);
  par=sysreg_read_par();

  if(par & 0x1)
    return false;

  par &= 0xFFFFF000UL;
  *pa = par;
  return true;
}

/* main function to perform access control of uapp calls
 * acl is based upon code white-listing hashing
 */
void uapp_checkacl(uint32_t va){
  u32 paddr;

  //debug message
  #if 0
  _XDPRINTFSMP_("%s: enter\n", __func__);
  #endif
  
  if(!uapp_va2pa((uint32_t)va, &paddr)){
    //debug message
    #if 0
    _XDPRINTFSMP_("va to pa mapping=0x%08x\n", __func__, paddr);
    #endif
    //__SECURITY_ACTION__: no va to pa mapping in guest; fail silently for now
  }else{
    if(uapp_check_whitelist(paddr, WHITELIST_COMPARE_BYTES)){
      //debug
      #if 0
      _XDPRINTFSMP_("ACL passed\n");
      #endif

      // ACL check passed
    }else{
      //__SECURITY_ACTION__: acl check error; fail silently for now
    }
  }
  #if 0
  _XDPRINTFSMP_("%s: exit\n", __func__);
  #endif  
}
