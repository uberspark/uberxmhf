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

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uhsign.h>
#include <uberspark/uobjrtl/crypto/include/mac/hmacsha256/hmacsha256.h>
#include <uberspark/uobjrtl/crypto/include/basedefs.h>
//#include <uberspark/include/uberspark.h>


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
  uapp_checkacl(sysreg_read_elrhyp());

  //Call HMAC function
  unsigned long digest_size = HMAC_DIGEST_SIZE;
  unsigned char digest_result[HMAC_DIGEST_SIZE];

  if(uberspark_uobjrtl_crypto__mac_hmacsha256__hmac_sha256_memory(uhsign_key, (unsigned long) UHSIGN_KEY_SIZE, (unsigned char *) uhcp->pkt, (unsigned long) uhcp->pkt_size, &digest_result, &digest_size)==CRYPT_OK) {
    uberspark_uobjrtl_crt__memcpy(uhcp->digest, digest_result, HMAC_DIGEST_SIZE);

    return true;
  } else {
    return false;
  }
}
