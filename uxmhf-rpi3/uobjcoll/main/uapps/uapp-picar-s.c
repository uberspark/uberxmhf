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
	picar-s hypapp
	guest picar-s test 
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/debug.h>

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/picar-s.h>
//#include <uberspark/include/uberspark.h>
#include <uberspark/uobjrtl/crypto/include/mac/hmacsha256/hmacsha256.h>
#include <uberspark/uobjrtl/crypto/include/basedefs.h>
#include <uberspark/uobjrtl/crt/include/string.h>

#define MAX_LVL1_ENTRIES	4096
#define MAX_LVL2_ENTRIES	256

#define SIZEOF_LVL1_ENTRY_MAP	(1024*1024)	//each lvl1 entry maps to 1MB of memory
#define SIZEOF_LVL2_ENTRY_MAP	(1024*1024)	//each lvl1 entry maps to 1MB of memory


__attribute__((section(".data"))) static unsigned char uhsign_key_picar[]="super_secret_key_for_hmac";
#define UHSIGN_KEY_SIZE (sizeof(uhsign_key_picar))
#define HMAC_DIGEST_SIZE 32

//return true if handled the hypercall, false if not
bool uapp_picar_s_handlehcall(u32 picar_s_function, void *picar_s_buffer, u32 picar_s_buffer_len){
	picar_s_param_t *upicar;
	unsigned long digest_size = HMAC_DIGEST_SIZE;
	upicar = (picar_s_param_t *)picar_s_buffer;

	if(picar_s_function != UAPP_PICAR_S_FUNCTION_TEST)
		return false;

        if(uberspark_uobjrtl_crypto__mac_hmacsha256__hmac_sha256_memory(uhsign_key_picar, 
			(unsigned long) UHSIGN_KEY_SIZE, (unsigned char *) upicar->in, 
			(unsigned long) upicar->len, upicar->out, &digest_size)==CRYPT_OK) {
               _XDPRINTFSMP_("hmac call success\n");
        } 
	_XDPRINTFSMP_("%s: hcall: picar_s_function=0x%08x, picar_s_buffer=0x%08x, picar_s_buffer_len=0x%08x\n", __func__,
			picar_s_function, picar_s_buffer, picar_s_buffer_len);

	return true;
}
