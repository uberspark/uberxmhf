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

#ifndef __SHA256_H__
#define __SHA256_H__

#include <xmhfcrypto.h>

#define SHA2_RESULTLEN          (256/8)
#define SHA_DIGEST_LENGTH	SHA2_RESULTLEN

#ifndef __ASSEMBLY__

int sha256_compress(hash_state *md, const unsigned char *buf);
int sha256_init(hash_state * md);
int sha256_process (hash_state * md, const unsigned char *in,
		    unsigned long inlen);
int sha256_done(hash_state * md, unsigned char *out);
int sha256_memory(const unsigned char *in, unsigned long inlen,
		  unsigned char *out, unsigned long *outlen);
int sha256_memory_multi(unsigned char *out, unsigned long *outlen,
                        const unsigned char *in, unsigned long inlen, ...);
#endif // __ASSEMBLY__

#endif /* __SHA256_H__ */
