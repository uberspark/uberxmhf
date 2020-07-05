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

#ifndef __AES_H__
#define __AES_H__

#include <xmhfcrypto.h>

#define AES_KEY_LEN_BYTES	16

#ifndef __ASSEMBLY__

extern const struct ltc_cipher_descriptor rijndael_desc;

#define Te0(x) TE0[x]
#define Te1(x) TE1[x]
#define Te2(x) TE2[x]
#define Te3(x) TE3[x]

#define Td0(x) TD0[x]
#define Td1(x) TD1[x]
#define Td2(x) TD2[x]
#define Td3(x) TD3[x]

const u32 Te4[256];
const u32 Td4[256];


extern const u32 TE0[256];
extern const u32 TE1[256];
extern const u32 TE2[256];
extern const u32 TE3[256];


extern const u32 Te4_0[];
extern const u32 Te4_1[];
extern const u32 Te4_2[];
extern const u32 Te4_3[];

extern const u32 TD0[256];
extern const u32 TD1[256];
extern const u32 TD2[256];
extern const u32 TD3[256];

extern const u32 Tks0[];
extern const u32 Tks1[];
extern const u32 Tks2[];
extern const u32 Tks3[];

extern const u32 rcon[];

int rijndael_cbc_start(const unsigned char * IV, const unsigned char *key,
		       int keylen, int num_rounds, symmetric_CBC *cbc);
int rijndael_cbc_encrypt(const unsigned char *pt, unsigned char *ct, unsigned long len, symmetric_CBC *cbc);
int rijndael_cbc_done(symmetric_CBC *cbc);
int rijndael_cbc_decrypt(const unsigned char *ct, unsigned char *pt, unsigned long len, symmetric_CBC *cbc);



#endif // __ASSEMBLY__


#endif /* __AES_H__ */
