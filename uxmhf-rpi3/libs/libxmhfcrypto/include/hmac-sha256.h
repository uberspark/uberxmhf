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
 *         matt mccormack (matthew.mccormack@live.com)
 *
 */

#ifndef __HMAC_SHA256_H__
#define __HMAC_SHA256_H__

#ifndef __ASSEMBLY__

#include <xmhfcrypto.h>

int hmac_sha256_init(hmac_state *hmac, const unsigned char *key,
		     unsigned long keylen);
int hmac_sha256_process(hmac_state *hmac, const unsigned char *in,
		      unsigned long inlen);
int hmac_sha256_done(hmac_state *hmac, unsigned char *out,
    		     unsigned long *outlen);
int hmac_sha256_memory(const unsigned char *key,  unsigned long keylen,
                       const unsigned char *in,   unsigned long inlen,
                       unsigned char *out,  unsigned long *outlen);

#endif // __ASSEMBLY__

#endif /* __HMAC_SHA256_H__ */
