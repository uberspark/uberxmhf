/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

#ifndef __XMHFCRYPTO_H__
#define __XMHFCRYPTO_H__

#include <stdlib.h>
#include <stdio.h>

#define SHA1_RESULTLEN (160/8)
#define SHA_DIGEST_LENGTH	SHA1_RESULTLEN


//tomcrypt.h

/* max size of either a cipher/hash block or symmetric key [largest of the two] */
#define MAXBLOCKSIZE  128

/* descriptor table size */
#define TAB_SIZE      32

/* error codes [will be expanded in future releases] */
enum {
   CRYPT_OK=0,             /* Result OK */
   CRYPT_ERROR,            /* Generic Error */
   CRYPT_NOP,              /* Not a failure but no operation was performed */

   CRYPT_INVALID_KEYSIZE,  /* Invalid key size given */
   CRYPT_INVALID_ROUNDS,   /* Invalid number of rounds */
   CRYPT_FAIL_TESTVECTOR,  /* Algorithm failed test vectors */

   CRYPT_BUFFER_OVERFLOW,  /* Not enough space for output */
   CRYPT_INVALID_PACKET,   /* Invalid input packet given */

   CRYPT_INVALID_PRNGSIZE, /* Invalid number of bits for a PRNG */
   CRYPT_ERROR_READPRNG,   /* Could not read enough from PRNG */

   CRYPT_INVALID_CIPHER,   /* Invalid cipher specified */
   CRYPT_INVALID_HASH,     /* Invalid hash specified */
   CRYPT_INVALID_PRNG,     /* Invalid PRNG specified */

   CRYPT_MEM,              /* Out of memory */

   CRYPT_PK_TYPE_MISMATCH, /* Not equivalent types of PK keys */
   CRYPT_PK_NOT_PRIVATE,   /* Requires a private PK key */

   CRYPT_INVALID_ARG,      /* Generic invalid argument */
   CRYPT_FILE_NOTFOUND,    /* File Not Found */

   CRYPT_PK_INVALID_TYPE,  /* Invalid type of PK key */
   CRYPT_PK_INVALID_SYSTEM,/* Invalid PK system specified */
   CRYPT_PK_DUP,           /* Duplicate key already in key ring */
   CRYPT_PK_NOT_FOUND,     /* Key not found in keyring */
   CRYPT_PK_INVALID_SIZE,  /* Invalid size input for PK parameters */

   CRYPT_INVALID_PRIME_SIZE,/* Invalid size of prime requested */
   CRYPT_PK_INVALID_PADDING /* Invalid padding on input */
};

//tomcrypt_macros.h
#define STORE32H(x, y)                                                                     \
     { (y)[0] = (unsigned char)(((x)>>24)&255); (y)[1] = (unsigned char)(((x)>>16)&255);   \
       (y)[2] = (unsigned char)(((x)>>8)&255); (y)[3] = (unsigned char)((x)&255); }

#define LOAD32H(x, y)                            \
     { x = ((unsigned long)((y)[0] & 255)<<24) | \
           ((unsigned long)((y)[1] & 255)<<16) | \
           ((unsigned long)((y)[2] & 255)<<8)  | \
           ((unsigned long)((y)[3] & 255)); }

#define STORE64H(x, y)                                                                     \
   { (y)[0] = (unsigned char)(((x)>>56)&255); (y)[1] = (unsigned char)(((x)>>48)&255);     \
     (y)[2] = (unsigned char)(((x)>>40)&255); (y)[3] = (unsigned char)(((x)>>32)&255);     \
     (y)[4] = (unsigned char)(((x)>>24)&255); (y)[5] = (unsigned char)(((x)>>16)&255);     \
     (y)[6] = (unsigned char)(((x)>>8)&255); (y)[7] = (unsigned char)((x)&255); }

#ifndef MIN
   #define MIN(x, y) ( ((x)<(y))?(x):(y) )
#endif

/* rotates the hard way */
#define ROL(x, y) ( (((unsigned long)(x)<<(unsigned long)((y)&31)) | (((unsigned long)(x)&0xFFFFFFFFUL)>>(unsigned long)(32-((y)&31)))) & 0xFFFFFFFFUL)
#define ROR(x, y) ( ((((unsigned long)(x)&0xFFFFFFFFUL)>>(unsigned long)((y)&31)) | ((unsigned long)(x)<<(unsigned long)(32-((y)&31)))) & 0xFFFFFFFFUL)
#define ROLc(x, y) ( (((unsigned long)(x)<<(unsigned long)((y)&31)) | (((unsigned long)(x)&0xFFFFFFFFUL)>>(unsigned long)(32-((y)&31)))) & 0xFFFFFFFFUL)
#define RORc(x, y) ( ((((unsigned long)(x)&0xFFFFFFFFUL)>>(unsigned long)((y)&31)) | ((unsigned long)(x)<<(unsigned long)(32-((y)&31)))) & 0xFFFFFFFFUL)

/* extract a byte portably */
#define byte(x, n) (((x) >> (8 * (n))) & 255)


//tomcrypt_cipher.h

struct rijndael_key {
   u32 eK[60], dK[60];
   int Nr;
};

typedef union Symmetric_key {
   struct rijndael_key rijndael;
   void   *data;
} symmetric_key;

/** A block cipher CBC structure */
typedef struct {
   /** The index of the cipher chosen */
   int                 cipher, 
   /** The block size of the given cipher */                        
                       blocklen;
   /** The current IV */
   unsigned char       IV[MAXBLOCKSIZE];
   /** The scheduled key */
   symmetric_key       key;
} symmetric_CBC;


/** cipher descriptor table, last entry has "name == NULL" to mark the end of table */
extern struct ltc_cipher_descriptor {
   /** name of cipher */
   char *name;
   /** internal ID */
   unsigned char ID;
   /** min keysize (octets) */
   int  min_key_length, 
   /** max keysize (octets) */
        max_key_length, 
   /** block size (octets) */
        block_length, 
   /** default number of rounds */
        default_rounds;
   /** Setup the cipher 
      @param key         The input symmetric key
      @param keylen      The length of the input key (octets)
      @param num_rounds  The requested number of rounds (0==default)
      @param skey        [out] The destination of the scheduled key
      @return CRYPT_OK if successful
   */
   int  (*setup)(const unsigned char *key, int keylen, int num_rounds, symmetric_key *skey);
   /** Encrypt a block
      @param pt      The plaintext
      @param ct      [out] The ciphertext
      @param skey    The scheduled key
      @return CRYPT_OK if successful
   */
   int (*ecb_encrypt)(const unsigned char *pt, unsigned char *ct, symmetric_key *skey);
   /** Decrypt a block
      @param ct      The ciphertext
      @param pt      [out] The plaintext
      @param skey    The scheduled key
      @return CRYPT_OK if successful
   */
   int (*ecb_decrypt)(const unsigned char *ct, unsigned char *pt, symmetric_key *skey);
   /** Test the block cipher
       @return CRYPT_OK if successful, CRYPT_NOP if self-testing has been disabled
   */
   int (*test)(void);

   /** Terminate the context 
      @param skey    The scheduled key
   */
   void (*done)(symmetric_key *skey);      

   /** Determine a key size
       @param keysize    [in/out] The size of the key desired and the suggested size
       @return CRYPT_OK if successful
   */
   int  (*keysize)(int *keysize);

/** Accelerators **/
   /** Accelerated ECB encryption 
       @param pt      Plaintext
       @param ct      Ciphertext
       @param blocks  The number of complete blocks to process
       @param skey    The scheduled key context
       @return CRYPT_OK if successful
   */
   int (*accel_ecb_encrypt)(const unsigned char *pt, unsigned char *ct, unsigned long blocks, symmetric_key *skey);

   /** Accelerated ECB decryption 
       @param pt      Plaintext
       @param ct      Ciphertext
       @param blocks  The number of complete blocks to process
       @param skey    The scheduled key context
       @return CRYPT_OK if successful
   */
   int (*accel_ecb_decrypt)(const unsigned char *ct, unsigned char *pt, unsigned long blocks, symmetric_key *skey);

   /** Accelerated CBC encryption 
       @param pt      Plaintext
       @param ct      Ciphertext
       @param blocks  The number of complete blocks to process
       @param IV      The initial value (input/output)
       @param skey    The scheduled key context
       @return CRYPT_OK if successful
   */
   int (*accel_cbc_encrypt)(const unsigned char *pt, unsigned char *ct, unsigned long blocks, unsigned char *IV, symmetric_key *skey);

   /** Accelerated CBC decryption 
       @param pt      Plaintext
       @param ct      Ciphertext
       @param blocks  The number of complete blocks to process
       @param IV      The initial value (input/output)
       @param skey    The scheduled key context
       @return CRYPT_OK if successful
   */
   int (*accel_cbc_decrypt)(const unsigned char *ct, unsigned char *pt, unsigned long blocks, unsigned char *IV, symmetric_key *skey);

   /** Accelerated CTR encryption 
       @param pt      Plaintext
       @param ct      Ciphertext
       @param blocks  The number of complete blocks to process
       @param IV      The initial value (input/output)
       @param mode    little or big endian counter (mode=0 or mode=1)
       @param skey    The scheduled key context
       @return CRYPT_OK if successful
   */
   int (*accel_ctr_encrypt)(const unsigned char *pt, unsigned char *ct, unsigned long blocks, unsigned char *IV, int mode, symmetric_key *skey);

   /** Accelerated LRW 
       @param pt      Plaintext
       @param ct      Ciphertext
       @param blocks  The number of complete blocks to process
       @param IV      The initial value (input/output)
       @param tweak   The LRW tweak
       @param skey    The scheduled key context
       @return CRYPT_OK if successful
   */
   int (*accel_lrw_encrypt)(const unsigned char *pt, unsigned char *ct, unsigned long blocks, unsigned char *IV, const unsigned char *tweak, symmetric_key *skey);

   /** Accelerated LRW 
       @param ct      Ciphertext
       @param pt      Plaintext
       @param blocks  The number of complete blocks to process
       @param IV      The initial value (input/output)
       @param tweak   The LRW tweak
       @param skey    The scheduled key context
       @return CRYPT_OK if successful
   */
   int (*accel_lrw_decrypt)(const unsigned char *ct, unsigned char *pt, unsigned long blocks, unsigned char *IV, const unsigned char *tweak, symmetric_key *skey);

   /** Accelerated CCM packet (one-shot)
       @param key        The secret key to use
       @param keylen     The length of the secret key (octets)
       @param uskey      A previously scheduled key [optional can be NULL]
       @param nonce      The session nonce [use once]
       @param noncelen   The length of the nonce
       @param header     The header for the session
       @param headerlen  The length of the header (octets)
       @param pt         [out] The plaintext
       @param ptlen      The length of the plaintext (octets)
       @param ct         [out] The ciphertext
       @param tag        [out] The destination tag
       @param taglen     [in/out] The max size and resulting size of the authentication tag
       @param direction  Encrypt or Decrypt direction (0 or 1)
       @return CRYPT_OK if successful
   */
   int (*accel_ccm_memory)(
       const unsigned char *key,    unsigned long keylen,
       symmetric_key       *uskey,
       const unsigned char *nonce,  unsigned long noncelen,
       const unsigned char *header, unsigned long headerlen,
             unsigned char *pt,     unsigned long ptlen,
             unsigned char *ct,
             unsigned char *tag,    unsigned long *taglen,
                       int  direction);

   /** Accelerated GCM packet (one shot)
       @param key        The secret key
       @param keylen     The length of the secret key
       @param IV         The initial vector 
       @param IVlen      The length of the initial vector
       @param adata      The additional authentication data (header)
       @param adatalen   The length of the adata
       @param pt         The plaintext
       @param ptlen      The length of the plaintext (ciphertext length is the same)
       @param ct         The ciphertext
       @param tag        [out] The MAC tag
       @param taglen     [in/out] The MAC tag length
       @param direction  Encrypt or Decrypt mode (GCM_ENCRYPT or GCM_DECRYPT)
       @return CRYPT_OK on success
   */
   int (*accel_gcm_memory)(
       const unsigned char *key,    unsigned long keylen,
       const unsigned char *IV,     unsigned long IVlen,
       const unsigned char *adata,  unsigned long adatalen,
             unsigned char *pt,     unsigned long ptlen,
             unsigned char *ct, 
             unsigned char *tag,    unsigned long *taglen,
                       int direction);

   /** Accelerated one shot LTC_OMAC 
       @param key            The secret key
       @param keylen         The key length (octets) 
       @param in             The message 
       @param inlen          Length of message (octets)
       @param out            [out] Destination for tag
       @param outlen         [in/out] Initial and final size of out
       @return CRYPT_OK on success
   */
   int (*omac_memory)(
       const unsigned char *key, unsigned long keylen,
       const unsigned char *in,  unsigned long inlen,
             unsigned char *out, unsigned long *outlen);

   /** Accelerated one shot XCBC 
       @param key            The secret key
       @param keylen         The key length (octets) 
       @param in             The message 
       @param inlen          Length of message (octets)
       @param out            [out] Destination for tag
       @param outlen         [in/out] Initial and final size of out
       @return CRYPT_OK on success
   */
   int (*xcbc_memory)(
       const unsigned char *key, unsigned long keylen,
       const unsigned char *in,  unsigned long inlen,
             unsigned char *out, unsigned long *outlen);

   /** Accelerated one shot F9 
       @param key            The secret key
       @param keylen         The key length (octets) 
       @param in             The message 
       @param inlen          Length of message (octets)
       @param out            [out] Destination for tag
       @param outlen         [in/out] Initial and final size of out
       @return CRYPT_OK on success
       @remark Requires manual padding
   */
   int (*f9_memory)(
       const unsigned char *key, unsigned long keylen,
       const unsigned char *in,  unsigned long inlen,
             unsigned char *out, unsigned long *outlen);
} cipher_descriptor[];

int register_cipher(const struct ltc_cipher_descriptor *cipher);
int find_cipher(const char *name);
int cipher_is_valid(int idx);


//tomcrypt_hash.h
struct sha1_state {
    u64 length;
    u32 state[5], curlen;
    u8 buf[64];
};


typedef union Hash_state {
    char dummy[1];
    struct sha1_state sha1;
    void *data;
} hash_state;

/** hash descriptor */
extern  struct ltc_hash_descriptor {
    /** name of hash */
    char *name;
    /** internal ID */
    unsigned char ID;
    /** Size of digest in octets */
    unsigned long hashsize;
    /** Input block size in octets */
    unsigned long blocksize;
    /** ASN.1 OID */
    unsigned long OID[16];
    /** Length of DER encoding */
    unsigned long OIDlen;

    /** Init a hash state
      @param hash   The hash to initialize
      @return CRYPT_OK if successful
    */
    int (*init)(hash_state *hash);
    /** Process a block of data 
      @param hash   The hash state
      @param in     The data to hash
      @param inlen  The length of the data (octets)
      @return CRYPT_OK if successful
    */
    int (*process)(hash_state *hash, const unsigned char *in, unsigned long inlen);
    /** Produce the digest and store it
      @param hash   The hash state
      @param out    [out] The destination of the digest
      @return CRYPT_OK if successful
    */
    int (*done)(hash_state *hash, unsigned char *out);
    /** Self-test
      @return CRYPT_OK if successful, CRYPT_NOP if self-tests have been disabled
    */
    int (*test)(void);

    /* accelerated hmac callback: if you need to-do multiple packets just use the generic hmac_memory and provide a hash callback */
    int  (*hmac_block)(const unsigned char *key, unsigned long  keylen,
                       const unsigned char *in,  unsigned long  inlen, 
                             unsigned char *out, unsigned long *outlen);

} hash_descriptor[];

/* a simple macro for making hash "process" functions */
#define HASH_PROCESS(func_name, compress_name, state_var, block_size)                       \
int func_name (hash_state * md, const unsigned char *in, unsigned long inlen)               \
{                                                                                           \
    unsigned long n;                                                                        \
    int           err;                                                                      \
    assert(md != NULL);                                                                 \
    assert(in != NULL);                                                                 \
    if (md-> state_var .curlen > sizeof(md-> state_var .buf)) {                             \
       return CRYPT_INVALID_ARG;                                                            \
    }                                                                                       \
    while (inlen > 0) {                                                                     \
        if (md-> state_var .curlen == 0 && inlen >= block_size) {                           \
           if ((err = compress_name (md, (unsigned char *)in)) != CRYPT_OK) {               \
              return err;                                                                   \
           }                                                                                \
           md-> state_var .length += block_size * 8;                                        \
           in             += block_size;                                                    \
           inlen          -= block_size;                                                    \
        } else {                                                                            \
           n = MIN(inlen, (block_size - md-> state_var .curlen));                           \
           memcpy(md-> state_var .buf + md-> state_var.curlen, in, (size_t)n);              \
           md-> state_var .curlen += n;                                                     \
           in             += n;                                                             \
           inlen          -= n;                                                             \
           if (md-> state_var .curlen == block_size) {                                      \
              if ((err = compress_name (md, (unsigned char *)md-> state_var .buf)) != CRYPT_OK) {            \
                 return err;                                                                \
              }                                                                             \
              md-> state_var .length += 8*block_size;                                       \
              md-> state_var .curlen = 0;                                                   \
           }                                                                                \
       }                                                                                    \
    }                                                                                       \
    return CRYPT_OK;                                                                        \
}


int register_hash(const struct ltc_hash_descriptor *hash);
int find_hash(const char *name);
int hash_memory(int hash, const unsigned char *in, unsigned long inlen, unsigned char *out, unsigned long *outlen);
int hash_memory_multi(int hash, unsigned char *out, unsigned long *outlen,
                      const unsigned char *in, unsigned long inlen, ...);
int hash_is_valid(int idx);

//tomcrypt_mac.h
typedef struct Hmac_state {
     hash_state     md;
     int            hash;
     hash_state     hashstate;
     unsigned char  *key;
} hmac_state;



//tomcrypt_custom.h
/* default no functions */
#define LTC_MUTEX_GLOBAL(x)
#define LTC_MUTEX_PROTO(x)
#define LTC_MUTEX_TYPE(x)
#define LTC_MUTEX_INIT(x)
#define LTC_MUTEX_LOCK(x)
#define LTC_MUTEX_UNLOCK(x)

extern void *malloc(size_t size);
extern void free(void *s);
extern void *calloc(size_t num, size_t size);
extern void *realloc(void *p, size_t n);
extern void	 qsort(void *base, size_t nmemb, size_t size,
	    int (*compar)(const void *, const void *));      

#define XMEMCMP  memcmp
#define XMEMCPY  memcpy
#define XMEMSET	 memset
#define XMALLOC  malloc
#define XCALLOC  calloc
#define XREALLOC realloc
#define XQSORT	 qsort
#define XFREE    free
#define XSTRCMP	 strcmp

//tomcrypt_prng.h

typedef union Prng_state {
    char dummy[1];
} prng_state;

/** PRNG descriptor */
extern struct ltc_prng_descriptor {
    /** Name of the PRNG */
    char *name;
    /** size in bytes of exported state */
    int  export_size;
    /** Start a PRNG state
        @param prng   [out] The state to initialize
        @return CRYPT_OK if successful
    */
    int (*start)(prng_state *prng);
    /** Add entropy to the PRNG
        @param in         The entropy
        @param inlen      Length of the entropy (octets)\
        @param prng       The PRNG state
        @return CRYPT_OK if successful
    */
    int (*add_entropy)(const unsigned char *in, unsigned long inlen, prng_state *prng);
    /** Ready a PRNG state to read from
        @param prng       The PRNG state to ready
        @return CRYPT_OK if successful
    */
    int (*ready)(prng_state *prng);
    /** Read from the PRNG
        @param out     [out] Where to store the data
        @param outlen  Length of data desired (octets)
        @param prng    The PRNG state to read from
        @return Number of octets read
    */
    unsigned long (*read)(unsigned char *out, unsigned long outlen, prng_state *prng);
    /** Terminate a PRNG state
        @param prng   The PRNG state to terminate
        @return CRYPT_OK if successful
    */
    int (*done)(prng_state *prng);
    /** Export a PRNG state  
        @param out     [out] The destination for the state
        @param outlen  [in/out] The max size and resulting size of the PRNG state
        @param prng    The PRNG to export
        @return CRYPT_OK if successful
    */
    int (*pexport)(unsigned char *out, unsigned long *outlen, prng_state *prng);
    /** Import a PRNG state
        @param in      The data to import
        @param inlen   The length of the data to import (octets)
        @param prng    The PRNG to initialize/import
        @return CRYPT_OK if successful
    */
    int (*pimport)(const unsigned char *in, unsigned long inlen, prng_state *prng);
    /** Self-test the PRNG
        @return CRYPT_OK if successful, CRYPT_NOP if self-testing has been disabled
    */
    int (*test)(void);
} prng_descriptor[];

int prng_is_valid(int idx);
int register_prng(const struct ltc_prng_descriptor *prng);

LTC_MUTEX_PROTO(ltc_prng_mutex)

//tomcrypt_pk.h
/* ---- NUMBER THEORY ---- */

enum {
   PK_PUBLIC=0,
   PK_PRIVATE=1
};


/* ---- RSA ---- */
/* Min and Max RSA key sizes (in bits) */
#define MIN_RSA_SIZE 1024
#define MAX_RSA_SIZE 4096

/** RSA LTC_PKCS style key */
typedef struct Rsa_key {
    /** Type of key, PK_PRIVATE or PK_PUBLIC */
    int type;
    /** The public exponent */
    void *e; 
    /** The private exponent */
    void *d; 
    /** The modulus */
    void *N; 
    /** The p factor of N */
    void *p; 
    /** The q factor of N */
    void *q; 
    /** The 1/q mod p CRT param */
    void *qP; 
    /** The d mod (p - 1) CRT param */
    void *dP; 
    /** The d mod (q - 1) CRT param */
    void *dQ;
} rsa_key;


/** A point on a ECC curve, stored in Jacbobian format such that (x,y,z) => (x/z^2, y/z^3, 1) when interpretted as affine */
typedef struct {
    /** The x co-ordinate */
    void *x;

    /** The y co-ordinate */
    void *y;

    /** The z co-ordinate */
    void *z;
} ecc_point;


/* DER handling */

enum {
 LTC_ASN1_EOL,
 LTC_ASN1_BOOLEAN,
 LTC_ASN1_INTEGER,
 LTC_ASN1_SHORT_INTEGER,
 LTC_ASN1_BIT_STRING,
 LTC_ASN1_OCTET_STRING,
 LTC_ASN1_NULL,
 LTC_ASN1_OBJECT_IDENTIFIER,
 LTC_ASN1_IA5_STRING,
 LTC_ASN1_PRINTABLE_STRING,
 LTC_ASN1_UTF8_STRING,
 LTC_ASN1_UTCTIME,
 LTC_ASN1_CHOICE,
 LTC_ASN1_SEQUENCE,
 LTC_ASN1_SET,
 LTC_ASN1_SETOF
};

/** A LTC ASN.1 list type */
typedef struct ltc_asn1_list_ {
   /** The LTC ASN.1 enumerated type identifier */
   int           type;
   /** The data to encode or place for decoding */
   void         *data;
   /** The size of the input or resulting output */
   unsigned long size;
   /** The used flag, this is used by the CHOICE ASN.1 type to indicate which choice was made */
   int           used;
   /** prev/next entry in the list */
   struct ltc_asn1_list_ *prev, *next, *child, *parent;
} ltc_asn1_list;

#define LTC_SET_ASN1(list, index, Type, Data, Size)  \
   do {                                              \
      int LTC_MACRO_temp            = (index);       \
      ltc_asn1_list *LTC_MACRO_list = (list);        \
      LTC_MACRO_list[LTC_MACRO_temp].type = (Type);  \
      LTC_MACRO_list[LTC_MACRO_temp].data = (void*)(Data);  \
      LTC_MACRO_list[LTC_MACRO_temp].size = (Size);  \
      LTC_MACRO_list[LTC_MACRO_temp].used = 0;       \
   } while (0);

/* SEQUENCE */
int der_encode_sequence_ex(ltc_asn1_list *list, unsigned long inlen,
                           unsigned char *out,  unsigned long *outlen, int type_of);
                          
#define der_encode_sequence(list, inlen, out, outlen) der_encode_sequence_ex(list, inlen, out, outlen, LTC_ASN1_SEQUENCE)                        

int der_decode_sequence_ex(const unsigned char *in, unsigned long  inlen,
                           ltc_asn1_list *list,     unsigned long  outlen, int ordered);
                              
#define der_decode_sequence(in, inlen, list, outlen) der_decode_sequence_ex(in, inlen, list, outlen, 1)

int der_length_sequence(ltc_asn1_list *list, unsigned long inlen,
                        unsigned long *outlen);

/* SET */
#define der_decode_set(in, inlen, list, outlen) der_decode_sequence_ex(in, inlen, list, outlen, 0)
#define der_length_set der_length_sequence
int der_encode_set(ltc_asn1_list *list, unsigned long inlen,
                   unsigned char *out,  unsigned long *outlen);

int der_encode_setof(ltc_asn1_list *list, unsigned long inlen,
                     unsigned char *out,  unsigned long *outlen);
                        
/* VA list handy helpers with triplets of <type, size, data> */
int der_encode_sequence_multi(unsigned char *out, unsigned long *outlen, ...);
int der_decode_sequence_multi(const unsigned char *in, unsigned long inlen, ...);

/* FLEXI DECODER handle unknown list decoder */
/*int  der_decode_sequence_flexi(const unsigned char *in, unsigned long *inlen, ltc_asn1_list **out);
void der_free_sequence_flexi(ltc_asn1_list *list);
void der_sequence_free(ltc_asn1_list *in);
*/

/* BOOLEAN */
int der_length_boolean(unsigned long *outlen);
int der_encode_boolean(int in, 
                       unsigned char *out, unsigned long *outlen);
int der_decode_boolean(const unsigned char *in, unsigned long inlen,
                                       int *out);		       
/* INTEGER */
int der_encode_integer(void *num, unsigned char *out, unsigned long *outlen);
int der_decode_integer(const unsigned char *in, unsigned long inlen, void *num);
int der_length_integer(void *num, unsigned long *len);

/* INTEGER -- handy for 0..2^32-1 values */
int der_decode_short_integer(const unsigned char *in, unsigned long inlen, unsigned long *num);
int der_encode_short_integer(unsigned long num, unsigned char *out, unsigned long *outlen);
int der_length_short_integer(unsigned long num, unsigned long *outlen);

/* BIT STRING */
int der_encode_bit_string(const unsigned char *in, unsigned long inlen,
                                unsigned char *out, unsigned long *outlen);
int der_decode_bit_string(const unsigned char *in, unsigned long inlen,
                                unsigned char *out, unsigned long *outlen);
int der_length_bit_string(unsigned long nbits, unsigned long *outlen);

/* OCTET STRING */
int der_encode_octet_string(const unsigned char *in, unsigned long inlen,
                                  unsigned char *out, unsigned long *outlen);
int der_decode_octet_string(const unsigned char *in, unsigned long inlen,
                                  unsigned char *out, unsigned long *outlen);
int der_length_octet_string(unsigned long noctets, unsigned long *outlen);

/* OBJECT IDENTIFIER */
int der_encode_object_identifier(unsigned long *words, unsigned long  nwords,
                                 unsigned char *out,   unsigned long *outlen);
int der_decode_object_identifier(const unsigned char *in,    unsigned long  inlen,
                                       unsigned long *words, unsigned long *outlen);
int der_length_object_identifier(unsigned long *words, unsigned long nwords, unsigned long *outlen);
unsigned long der_object_identifier_bits(unsigned long x);

/* IA5 STRING */
int der_encode_ia5_string(const unsigned char *in, unsigned long inlen,
                                unsigned char *out, unsigned long *outlen);
int der_decode_ia5_string(const unsigned char *in, unsigned long inlen,
                                unsigned char *out, unsigned long *outlen);
int der_length_ia5_string(const unsigned char *octets, unsigned long noctets, unsigned long *outlen);

int der_ia5_char_encode(int c);
int der_ia5_value_decode(int v);

/* Printable STRING */
int der_encode_printable_string(const unsigned char *in, unsigned long inlen,
                                unsigned char *out, unsigned long *outlen);
int der_decode_printable_string(const unsigned char *in, unsigned long inlen,
                                unsigned char *out, unsigned long *outlen);
int der_length_printable_string(const unsigned char *octets, unsigned long noctets, unsigned long *outlen);

int der_printable_char_encode(int c);
int der_printable_value_decode(int v);

typedef u32 wchar_t;

int der_encode_utf8_string(const wchar_t *in,  unsigned long inlen,
                           unsigned char *out, unsigned long *outlen);

int der_decode_utf8_string(const unsigned char *in,  unsigned long inlen,
                                       wchar_t *out, unsigned long *outlen);
unsigned long der_utf8_charsize(const wchar_t c);
int der_length_utf8_string(const wchar_t *in, unsigned long noctets, unsigned long *outlen);


/* CHOICE */
int der_decode_choice(const unsigned char *in,   unsigned long *inlen,
                            ltc_asn1_list *list, unsigned long  outlen);

/* UTCTime */
typedef struct {
   unsigned YY, /* year */
            MM, /* month */
            DD, /* day */
            hh, /* hour */
            mm, /* minute */
            ss, /* second */
            off_dir, /* timezone offset direction 0 == +, 1 == - */
            off_hh, /* timezone offset hours */
            off_mm; /* timezone offset minutes */
} ltc_utctime;

int der_encode_utctime(ltc_utctime *utctime, 
                       unsigned char *out,   unsigned long *outlen);

int der_decode_utctime(const unsigned char *in, unsigned long *inlen,
                             ltc_utctime   *out);

int der_length_utctime(ltc_utctime *utctime, unsigned long *outlen);



//tomcrypt_math.h

/** math functions **/

#define LTC_MP_LT   -1
#define LTC_MP_EQ    0
#define LTC_MP_GT    1

#define LTC_MP_NO    0
#define LTC_MP_YES   1


/** math descriptor */
typedef struct {
   /** Name of the math provider */
   char *name;

   /** Bits per digit, amount of bits must fit in an unsigned long */
   int  bits_per_digit;

/* ---- init/deinit functions ---- */

   /** initialize a bignum
     @param   a     The number to initialize
     @return  CRYPT_OK on success
   */
   int (*init)(void **a);
   
   /** init copy 
     @param  dst    The number to initialize and write to
     @param  src    The number to copy from
     @return CRYPT_OK on success
   */
   int (*init_copy)(void **dst, void *src);

   /** deinit 
      @param   a    The number to free
      @return CRYPT_OK on success
   */
   void (*deinit)(void *a);

/* ---- data movement ---- */

   /** negate
      @param   src   The number to negate
      @param   dst   The destination
      @return CRYPT_OK on success
   */
   int (*neg)(void *src, void *dst);
   
   /** copy 
      @param   src   The number to copy from
      @param   dst   The number to write to 
      @return CRYPT_OK on success
   */
   int (*copy)(void *src, void *dst);

/* ---- trivial low level functions ---- */

   /** set small constant 
      @param a    Number to write to
      @param n    Source upto bits_per_digit (actually meant for very small constants) 
      @return CRYPT_OK on succcess
   */
   int (*set_int)(void *a, unsigned long n);

   /** get small constant 
      @param a    Number to read, only fetches upto bits_per_digit from the number
      @return  The lower bits_per_digit of the integer (unsigned)
   */
   unsigned long (*get_int)(void *a);

   /** get digit n 
     @param a  The number to read from
     @param n  The number of the digit to fetch
     @return  The bits_per_digit  sized n'th digit of a
   */
   unsigned long (*get_digit)(void *a, int n);

   /** Get the number of digits that represent the number
     @param a   The number to count
     @return The number of digits used to represent the number
   */
   int (*get_digit_count)(void *a);

   /** compare two integers
     @param a   The left side integer
     @param b   The right side integer
     @return LTC_MP_LT if a < b, LTC_MP_GT if a > b and LTC_MP_EQ otherwise.  (signed comparison)
   */
   int (*compare)(void *a, void *b);

   /** compare against int 
     @param a   The left side integer
     @param b   The right side integer (upto bits_per_digit)
     @return LTC_MP_LT if a < b, LTC_MP_GT if a > b and LTC_MP_EQ otherwise.  (signed comparison)
   */
   int (*compare_d)(void *a, unsigned long n);

   /** Count the number of bits used to represent the integer
     @param a   The integer to count
     @return The number of bits required to represent the integer
   */
   int (*count_bits)(void * a);

   /** Count the number of LSB bits which are zero 
     @param a   The integer to count
     @return The number of contiguous zero LSB bits
   */
   int (*count_lsb_bits)(void *a);

   /** Compute a power of two
     @param a  The integer to store the power in
     @param n  The power of two you want to store (a = 2^n)
     @return CRYPT_OK on success
   */
   int (*twoexpt)(void *a , int n);

/* ---- radix conversions ---- */
   
   /** read ascii string 
     @param a     The integer to store into
     @param str   The string to read
     @param radix The radix the integer has been represented in (2-64)
     @return CRYPT_OK on success
   */
   int (*read_radix)(void *a, const char *str, int radix);

   /** write number to string
     @param a     The integer to store
     @param str   The destination for the string
     @param radix The radix the integer is to be represented in (2-64)
     @return CRYPT_OK on success
   */
   int (*write_radix)(void *a, char *str, int radix);

   /** get size as unsigned char string 
     @param a     The integer to get the size (when stored in array of octets)
     @return The length of the integer
   */
   unsigned long (*unsigned_size)(void *a);

   /** store an integer as an array of octets 
     @param src   The integer to store
     @param dst   The buffer to store the integer in
     @return CRYPT_OK on success
   */
   int (*unsigned_write)(void *src, unsigned char *dst);

   /** read an array of octets and store as integer
     @param dst   The integer to load
     @param src   The array of octets 
     @param len   The number of octets 
     @return CRYPT_OK on success
   */
   int (*unsigned_read)(void *dst, unsigned char *src, unsigned long len);

/* ---- basic math ---- */

   /** add two integers 
     @param a   The first source integer
     @param b   The second source integer
     @param c   The destination of "a + b"
     @return CRYPT_OK on success
   */
   int (*add)(void *a, void *b, void *c);


   /** add two integers 
     @param a   The first source integer
     @param b   The second source integer (single digit of upto bits_per_digit in length)
     @param c   The destination of "a + b"
     @return CRYPT_OK on success
   */
   int (*addi)(void *a, unsigned long b, void *c);

   /** subtract two integers 
     @param a   The first source integer
     @param b   The second source integer
     @param c   The destination of "a - b"
     @return CRYPT_OK on success
   */
   int (*sub)(void *a, void *b, void *c);

   /** subtract two integers 
     @param a   The first source integer
     @param b   The second source integer (single digit of upto bits_per_digit in length)
     @param c   The destination of "a - b"
     @return CRYPT_OK on success
   */
   int (*subi)(void *a, unsigned long b, void *c);

   /** multiply two integers 
     @param a   The first source integer
     @param b   The second source integer (single digit of upto bits_per_digit in length)
     @param c   The destination of "a * b"
     @return CRYPT_OK on success
   */
   int (*mul)(void *a, void *b, void *c);

   /** multiply two integers 
     @param a   The first source integer
     @param b   The second source integer (single digit of upto bits_per_digit in length)
     @param c   The destination of "a * b"
     @return CRYPT_OK on success
   */
   int (*muli)(void *a, unsigned long b, void *c);

   /** Square an integer
     @param a    The integer to square
     @param b    The destination
     @return CRYPT_OK on success
   */
   int (*sqr)(void *a, void *b);

   /** Divide an integer
     @param a    The dividend
     @param b    The divisor
     @param c    The quotient (can be NULL to signify don't care)
     @param d    The remainder (can be NULL to signify don't care)
     @return CRYPT_OK on success
   */
   int (*mpdiv)(void *a, void *b, void *c, void *d);

   /** divide by two 
      @param  a   The integer to divide (shift right)
      @param  b   The destination 
      @return CRYPT_OK on success
   */
   int (*div_2)(void *a, void *b);

   /** Get remainder (small value)
      @param  a    The integer to reduce
      @param  b    The modulus (upto bits_per_digit in length)
      @param  c    The destination for the residue
      @return CRYPT_OK on success
   */
   int (*modi)(void *a, unsigned long b, unsigned long *c);

   /** gcd 
      @param  a     The first integer
      @param  b     The second integer
      @param  c     The destination for (a, b)
      @return CRYPT_OK on success
   */
   int (*gcd)(void *a, void *b, void *c);

   /** lcm 
      @param  a     The first integer
      @param  b     The second integer
      @param  c     The destination for [a, b]
      @return CRYPT_OK on success
   */
   int (*lcm)(void *a, void *b, void *c);

   /** Modular multiplication
      @param  a     The first source
      @param  b     The second source 
      @param  c     The modulus
      @param  d     The destination (a*b mod c)
      @return CRYPT_OK on success
   */
   int (*mulmod)(void *a, void *b, void *c, void *d);

   /** Modular squaring
      @param  a     The first source
      @param  b     The modulus
      @param  c     The destination (a*a mod b)
      @return CRYPT_OK on success
   */
   int (*sqrmod)(void *a, void *b, void *c);

   /** Modular inversion
      @param  a     The value to invert
      @param  b     The modulus 
      @param  c     The destination (1/a mod b)
      @return CRYPT_OK on success
   */
   int (*invmod)(void *, void *, void *);

/* ---- reduction ---- */

   /** setup montgomery
       @param a  The modulus 
       @param b  The destination for the reduction digit 
       @return CRYPT_OK on success
   */
   int (*montgomery_setup)(void *a, void **b);

   /** get normalization value 
       @param a   The destination for the normalization value
       @param b   The modulus
       @return  CRYPT_OK on success
   */
   int (*montgomery_normalization)(void *a, void *b);

   /** reduce a number
       @param a   The number [and dest] to reduce
       @param b   The modulus
       @param c   The value "b" from montgomery_setup()
       @return CRYPT_OK on success
   */
   int (*montgomery_reduce)(void *a, void *b, void *c);

   /** clean up  (frees memory)
       @param a   The value "b" from montgomery_setup()
       @return CRYPT_OK on success
   */      
   void (*montgomery_deinit)(void *a);

/* ---- exponentiation ---- */

   /** Modular exponentiation
       @param a    The base integer
       @param b    The power (can be negative) integer
       @param c    The modulus integer
       @param d    The destination
       @return CRYPT_OK on success
   */
   int (*exptmod)(void *a, void *b, void *c, void *d);

   /** Primality testing
       @param a     The integer to test
       @param b     The destination of the result (FP_YES if prime)
       @return CRYPT_OK on success
   */
   int (*isprime)(void *a, int *b);

/* ----  (optional) ecc point math ---- */

   /** ECC GF(p) point multiplication (from the NIST curves)
       @param k   The integer to multiply the point by
       @param G   The point to multiply
       @param R   The destination for kG  
       @param modulus  The modulus for the field
       @param map Boolean indicated whether to map back to affine or not (can be ignored if you work in affine only)
       @return CRYPT_OK on success
   */
   int (*INACTIVE_ecc_ptmul)(void *k, ecc_point *G, ecc_point *R, void *modulus, int map);

   /** ECC GF(p) point addition 
       @param P    The first point
       @param Q    The second point
       @param R    The destination of P + Q
       @param modulus  The modulus
       @param mp   The "b" value from montgomery_setup()
       @return CRYPT_OK on success
   */
   int (*INACTIVE_ecc_ptadd)(ecc_point *P, ecc_point *Q, ecc_point *R, void *modulus, void *mp);

   /** ECC GF(p) point double 
       @param P    The first point
       @param R    The destination of 2P
       @param modulus  The modulus
       @param mp   The "b" value from montgomery_setup()
       @return CRYPT_OK on success
   */
   int (*INACTIVE_ecc_ptdbl)(ecc_point *P, ecc_point *R, void *modulus, void *mp);

   /** ECC mapping from projective to affine, currently uses (x,y,z) => (x/z^2, y/z^3, 1)
       @param P     The point to map
       @param modulus The modulus
       @param mp    The "b" value from montgomery_setup()
       @return CRYPT_OK on success
       @remark  The mapping can be different but keep in mind a ecc_point only has three 
                integers (x,y,z) so if you use a different mapping you have to make it fit.
   */
   int (*INACTIVE_ecc_map)(ecc_point *P, void *modulus, void *mp);

   /** Computes kA*A + kB*B = C using Shamir's Trick
       @param A        First point to multiply
       @param kA       What to multiple A by
       @param B        Second point to multiply
       @param kB       What to multiple B by
       @param C        [out] Destination point (can overlap with A or B
       @param modulus  Modulus for curve 
       @return CRYPT_OK on success
   */ 
   int (*INACTIVE_ecc_mul2add)(ecc_point *A, void *kA,
                      ecc_point *B, void *kB,
                      ecc_point *C,
                           void *modulus);

/* ---- (optional) rsa optimized math (for internal CRT) ---- */

   /** RSA Key Generation 
       @param prng     An active PRNG state
       @param wprng    The index of the PRNG desired
       @param size     The size of the modulus (key size) desired (octets)
       @param e        The "e" value (public key).  e==65537 is a good choice
       @param key      [out] Destination of a newly created private key pair
       @return CRYPT_OK if successful, upon error all allocated ram is freed
    */
    int (*rsa_keygen)(prng_state *prng, int wprng, int size, long e, rsa_key *key);
   

   /** RSA exponentiation
      @param in       The octet array representing the base
      @param inlen    The length of the input
      @param out      The destination (to be stored in an octet array format)
      @param outlen   The length of the output buffer and the resulting size (zero padded to the size of the modulus)
      @param which    PK_PUBLIC for public RSA and PK_PRIVATE for private RSA
      @param key      The RSA key to use 
      @return CRYPT_OK on success
   */
   int (*rsa_me)(const unsigned char *in,   unsigned long inlen,
                       unsigned char *out,  unsigned long *outlen, int which,
                       rsa_key *key);
} ltc_math_descriptor;

extern ltc_math_descriptor ltc_mp;

extern const ltc_math_descriptor ltm_desc;

int ltc_init_multi(void **a, ...);
void ltc_deinit_multi(void *a, ...);
int rand_prime(void *N, long len, prng_state *prng, int wprng);


#if !defined(DESC_DEF_ONLY) && defined(LTC_SOURCE)


#define MP_DIGIT_BIT                 ltc_mp.bits_per_digit

/* some handy macros */
#define mp_init(a)                   ltc_mp.init(a)
#define mp_init_multi                ltc_init_multi
#define mp_clear(a)                  ltc_mp.deinit(a)
#define mp_clear_multi               ltc_deinit_multi
#define mp_init_copy(a, b)           ltc_mp.init_copy(a, b)

#define mp_neg(a, b)                 ltc_mp.neg(a, b)
#define mp_copy(a, b)                ltc_mp.copy(a, b)

#define mp_set(a, b)                 ltc_mp.set_int(a, b)
#define mp_set_int(a, b)             ltc_mp.set_int(a, b)
#define mp_get_int(a)                ltc_mp.get_int(a)
#define mp_get_digit(a, n)           ltc_mp.get_digit(a, n)
#define mp_get_digit_count(a)        ltc_mp.get_digit_count(a)
#define mp_cmp(a, b)                 ltc_mp.compare(a, b)
#define mp_cmp_d(a, b)               ltc_mp.compare_d(a, b)
#define mp_count_bits(a)             ltc_mp.count_bits(a)
#define mp_cnt_lsb(a)                ltc_mp.count_lsb_bits(a)
#define mp_2expt(a, b)               ltc_mp.twoexpt(a, b)

#define mp_read_radix(a, b, c)       ltc_mp.read_radix(a, b, c)
#define mp_toradix(a, b, c)          ltc_mp.write_radix(a, b, c)
#define mp_unsigned_bin_size(a)      ltc_mp.unsigned_size(a)
#define mp_to_unsigned_bin(a, b)     ltc_mp.unsigned_write(a, b)
#define mp_read_unsigned_bin(a, b, c) ltc_mp.unsigned_read(a, b, c)

#define mp_add(a, b, c)              ltc_mp.add(a, b, c)
#define mp_add_d(a, b, c)            ltc_mp.addi(a, b, c)
#define mp_sub(a, b, c)              ltc_mp.sub(a, b, c)
#define mp_sub_d(a, b, c)            ltc_mp.subi(a, b, c)
#define mp_mul(a, b, c)              ltc_mp.mul(a, b, c)
#define mp_mul_d(a, b, c)            ltc_mp.muli(a, b, c)
#define mp_sqr(a, b)                 ltc_mp.sqr(a, b)
#define mp_div(a, b, c, d)           ltc_mp.mpdiv(a, b, c, d)
#define mp_div_2(a, b)               ltc_mp.div_2(a, b)
#define mp_mod(a, b, c)              ltc_mp.mpdiv(a, b, NULL, c)
#define mp_mod_d(a, b, c)            ltc_mp.modi(a, b, c)
#define mp_gcd(a, b, c)              ltc_mp.gcd(a, b, c)
#define mp_lcm(a, b, c)              ltc_mp.lcm(a, b, c)

#define mp_mulmod(a, b, c, d)        ltc_mp.mulmod(a, b, c, d)
#define mp_sqrmod(a, b, c)           ltc_mp.sqrmod(a, b, c)
#define mp_invmod(a, b, c)           ltc_mp.invmod(a, b, c)

#define mp_montgomery_setup(a, b)    ltc_mp.montgomery_setup(a, b)
#define mp_montgomery_normalization(a, b) ltc_mp.montgomery_normalization(a, b)
#define mp_montgomery_reduce(a, b, c)   ltc_mp.montgomery_reduce(a, b, c)
#define mp_montgomery_free(a)        ltc_mp.montgomery_deinit(a)

#define mp_exptmod(a,b,c,d)          ltc_mp.exptmod(a,b,c,d)
#define mp_prime_is_prime(a, b, c)   ltc_mp.isprime(a, c)

#define mp_iszero(a)                 (mp_cmp_d(a, 0) == LTC_MP_EQ ? LTC_MP_YES : LTC_MP_NO)
#define mp_isodd(a)                  (mp_get_digit_count(a) > 0 ? (mp_get_digit(a, 0) & 1 ? LTC_MP_YES : LTC_MP_NO) : LTC_MP_NO)
#define mp_exch(a, b)                do { void *ABC__tmp = a; a = b; b = ABC__tmp; } while(0);

#define mp_tohex(a, b)               mp_toradix(a, b, 16)


#endif //!defined(DESC_DEF_ONLY) && defined(LTC_SOURCE)

//tommath.h

#ifndef MIN
   #define MIN(x,y) ((x)<(y)?(x):(y))
#endif

#ifndef MAX
   #define MAX(x,y) ((x)>(y)?(x):(y))
#endif

typedef int           mp_err;

typedef unsigned long      mp_digit;
typedef u64            mp_word;

#define CHAR_BIT 	8

/* default case is 28-bit digits, defines MP_28BIT as a handy macro to test */
#define DIGIT_BIT          28
#define MP_28BIT

/* C on the other hand doesn't care */
#define  OPT_CAST(x)

/* default precision */
#ifndef MP_PREC
   #ifndef MP_LOW_MEM
      #define MP_PREC                 32     /* default digits of precision */
   #else
      #define MP_PREC                 8      /* default digits of precision */
   #endif   
#endif

/* size of comba arrays, should be at least 2 * 2**(BITS_PER_WORD - BITS_PER_DIGIT*2) */
#define MP_WARRAY               (1 << (sizeof(mp_word) * CHAR_BIT - 2 * DIGIT_BIT + 1))


/* the infamous mp_int structure */
typedef struct  {
    int used, alloc, sign;
    mp_digit *dp;
} mp_int;

/* otherwise the bits per digit is calculated automatically from the size of a mp_digit */
#ifndef DIGIT_BIT
   #define DIGIT_BIT     ((int)((CHAR_BIT * sizeof(mp_digit) - 1)))  /* bits per digit */
#endif

#if (defined(DESC_DEF_ONLY) && defined(LTC_SOURCE)) || !defined(LTC_SOURCE)
	#define MP_DIGIT_BIT     DIGIT_BIT
#endif	

#define MP_MASK          ((((mp_digit)1)<<((mp_digit)DIGIT_BIT))-((mp_digit)1))
#define MP_DIGIT_MAX     MP_MASK

/* equalities */
#define MP_LT        -1   /* less than */
#define MP_EQ         0   /* equal to */
#define MP_GT         1   /* greater than */

#define MP_ZPOS       0   /* positive integer */
#define MP_NEG        1   /* negative */

#define MP_OKAY       0   /* ok result */
#define MP_MEM        -2  /* out of mem */
#define MP_VAL        -3  /* invalid input */
#define MP_RANGE      MP_VAL

#define MP_YES        1   /* yes response */
#define MP_NO         0   /* no response */

/* Primality generation flags */
#define LTM_PRIME_BBS      0x0001 /* BBS style prime */
#define LTM_PRIME_SAFE     0x0002 /* Safe prime (p-1)/2 == prime */
#define LTM_PRIME_2MSB_ON  0x0008 /* force 2nd MSB to 1 */

#define USED(m)    ((m)->used)
#define DIGIT(m,k) ((m)->dp[(k)])
#define SIGN(m)    ((m)->sign)


/* ---> Primes <--- */

/* number of primes */
#ifdef MP_8BIT
   #define PRIME_SIZE      31
#else
   #define PRIME_SIZE      256
#endif

#if (defined(DESC_DEF_ONLY) && defined(LTC_SOURCE)) || !defined(LTC_SOURCE)

	/* ---> Basic Manipulations <--- */
	#define mp_iszero(a) (((a)->used == 0) ? MP_YES : MP_NO)
	#define mp_iseven(a) (((a)->used > 0 && (((a)->dp[0] & 1) == 0)) ? MP_YES : MP_NO)
	#define mp_isodd(a)  (((a)->used > 0 && (((a)->dp[0] & 1) == 1)) ? MP_YES : MP_NO)

	/* table of first PRIME_SIZE primes */
	extern const mp_digit ltm_prime_tab[];


	int mp_montgomery_calc_normalization (mp_int * a, mp_int * b);
	int mp_mul_2(mp_int * a, mp_int * b);
	int mp_grow (mp_int * a, int size);
	int mp_cmp_mag (mp_int * a, mp_int * b);
	int s_mp_sub (mp_int * a, mp_int * b, mp_int * c);
	void mp_clamp (mp_int * a);

	int mp_init (mp_int * a);
	void mp_clear (mp_int * a);
	int mp_neg (mp_int * a, mp_int * b);
	int mp_copy (mp_int * a, mp_int * b);
	int mp_set_int (mp_int * a, unsigned long b);
	unsigned long mp_get_int(mp_int * a); 
	int mp_mul_2d (mp_int * a, int b, mp_int * c);
	int mp_lshd (mp_int * a, int b);
	int mp_cmp (mp_int * a, mp_int * b);
	int mp_cmp_d(mp_int * a, mp_digit b);
	int mp_count_bits (mp_int * a);
	int mp_cnt_lsb(mp_int *a);
	int mp_2expt (mp_int * a, int b);
	int mp_read_radix (mp_int * a, const char *str, int radix);
	void mp_zero (mp_int * a);
	int mp_toradix (mp_int * a, char *str, int radix);
	int mp_init_copy (mp_int * a, mp_int * b);
	int mp_unsigned_bin_size (mp_int * a);
	int mp_to_unsigned_bin (mp_int * a, unsigned char *b); //conf
	void bn_reverse (unsigned char *s, int len);
	int mp_read_unsigned_bin (mp_int * a, const unsigned char *b, int c);
	int mp_add (mp_int * a, mp_int * b, mp_int * c);
	int s_mp_add (mp_int * a, mp_int * b, mp_int * c);
	int mp_add_d (mp_int * a, mp_digit b, mp_int * c);
	int mp_sub (mp_int * a, mp_int * b, mp_int * c);
	int mp_sub_d (mp_int * a, mp_digit b, mp_int * c);
	int mp_mul (mp_int * a, mp_int * b, mp_int * c); //conf
	int mp_mul_d (mp_int * a, mp_digit b, mp_int * c);
	int mp_sqr (mp_int * a, mp_int * b); //conf
	int mp_div(mp_int * a, mp_int * b, mp_int * c, mp_int * d);
	int mp_div_2(mp_int * a, mp_int * b);
	int mp_mod_d (mp_int * a, mp_digit b, mp_digit * c);
	int mp_div_d (mp_int * a, mp_digit b, mp_int * c, mp_digit * d); //conf
	int mp_gcd (mp_int * a, mp_int * b, mp_int * c);
	int mp_lcm (mp_int * a, mp_int * b, mp_int * c);
	int mp_mulmod (mp_int * a, mp_int * b, mp_int * c, mp_int * d);
	int mp_sqrmod (mp_int * a, mp_int * b, mp_int * c);
	int mp_invmod (mp_int * a, mp_int * b, mp_int * c); //conf
	int mp_montgomery_setup (mp_int * n, mp_digit * rho); //conf
	int mp_montgomery_reduce (mp_int * x, mp_int * n, mp_digit rho);
	int mp_exptmod (mp_int * G, mp_int * X, mp_int * P, mp_int * Y); //conf
	int mp_prime_is_prime (mp_int * a, int t, int *result);
	void mp_set (mp_int * a, mp_digit b);
	int mp_div_2d (mp_int * a, int b, mp_int * c, mp_int * d);
	int mp_mod_2d (mp_int * a, int b, mp_int * c);
	void mp_rshd (mp_int * a, int b);
	void mp_exch (mp_int * a, mp_int * b);
	int s_mp_mul_digs (mp_int * a, mp_int * b, mp_int * c, int digs);
	int fast_s_mp_mul_digs (mp_int * a, mp_int * b, mp_int * c, int digs);
	#define s_mp_mul(a, b, c) s_mp_mul_digs(a, b, c, (a)->used + (b)->used + 1)
	int s_mp_sqr (mp_int * a, mp_int * b);
	int mp_init_multi(mp_int *mp, ...) ;
	int mp_init_size (mp_int * a, int size);
	void mp_clear_multi(mp_int *mp, ...);
	int mp_abs (mp_int * a, mp_int * b);
	int mp_mod (mp_int * a, mp_int * b, mp_int * c);
	int mp_invmod_slow (mp_int * a, mp_int * b, mp_int * c);
	int fast_mp_montgomery_reduce (mp_int * x, mp_int * n, mp_digit rho);
	int s_mp_exptmod (mp_int * G, mp_int * X, mp_int * P, mp_int * Y, int redmode); //conf
	int mp_reduce (mp_int * x, mp_int * m, mp_int * mu); //conf
	int s_mp_mul_high_digs (mp_int * a, mp_int * b, mp_int * c, int digs);
	int mp_reduce_setup (mp_int * a, mp_int * b);
	int mp_reduce_2k_setup(mp_int *a, mp_digit *d);
	int mp_reduce_2k_l(mp_int *a, mp_int *n, mp_int *d);
	int mp_reduce_2k_setup_l(mp_int *a, mp_int *d);
	int mp_prime_is_divisible (mp_int * a, int *result);
	int mp_prime_miller_rabin (mp_int * a, mp_int * b, int *result);

#endif //(defined(DESC_DEF_ONLY) && defined(LTC_SOURCE)) || !defined(LTC_SOURCE)




//tomcrypt_misc.h
/* ---- MEM routines ---- */
void zeromem(void *dst, size_t len);



//tomcrypt_argchk.h
//#define LTC_ARGCHK(x)	assert(x)
#define LTC_ARGCHK(x)	HALT_ON_ERRORCOND(x)
#define LTC_ARGCHKVD(x) LTC_ARGCHK(x)



//tomcrypt_pkcs.h

enum ltc_pkcs_1_v1_5_blocks
{
  LTC_LTC_PKCS_1_EMSA   = 1,        /* Block type 1 (LTC_PKCS #1 v1.5 signature padding) */
  LTC_LTC_PKCS_1_EME    = 2         /* Block type 2 (LTC_PKCS #1 v1.5 encryption padding) */
};

/* ===> LTC_PKCS #1 -- RSA Cryptography <=== */
enum ltc_pkcs_1_paddings
{
  LTC_LTC_PKCS_1_V1_5   = 1,        /* LTC_PKCS #1 v1.5 padding (\sa ltc_pkcs_1_v1_5_blocks) */
  LTC_LTC_PKCS_1_OAEP   = 2,        /* LTC_PKCS #1 v2.0 encryption padding */
  LTC_LTC_PKCS_1_PSS    = 3         /* LTC_PKCS #1 v2.1 signature padding */
};

int pkcs_1_mgf1(      int            hash_idx,
                const unsigned char *seed, unsigned long seedlen,
                      unsigned char *mask, unsigned long masklen);


/* *** v1.5 padding */
int pkcs_1_v1_5_encode(const unsigned char *msg, 
                             unsigned long  msglen,
                             int            block_type,
                             unsigned long  modulus_bitlen,
                                prng_state *prng, 
                                       int  prng_idx,
                             unsigned char *out, 
                             unsigned long *outlen);

int pkcs_1_v1_5_decode(const unsigned char *msg, 
                             unsigned long  msglen,
                                       int  block_type,
                             unsigned long  modulus_bitlen,
                             unsigned char *out, 
                             unsigned long *outlen,
                                       int *is_valid);

/* *** v2.1 padding */

int pkcs_1_pss_encode(const unsigned char *msghash, unsigned long msghashlen,
                            unsigned long saltlen,  prng_state   *prng,     
                            int           prng_idx, int           hash_idx,
                            unsigned long modulus_bitlen,
                            unsigned char *out,     unsigned long *outlen);

int pkcs_1_pss_decode(const unsigned char *msghash, unsigned long msghashlen,
                      const unsigned char *sig,     unsigned long siglen,
                            unsigned long saltlen,  int           hash_idx,
                            unsigned long modulus_bitlen, int    *res);


#include <sha1.h>
#include <aes.h>
#include <cbc.h>
#include <hmac.h>
#include <rsa.h>

#endif /* __XMHFCRYPTO_H__ */
