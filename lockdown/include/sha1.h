/**
 * sha1.h
 */
#ifndef _SHA1_H
#define _SHA1_H

#define SHA1_CHECKSUM_LEN	20
/*
 * SHA-1 context structure
 */
typedef struct
{
  unsigned long total[2];     /*!< number of bytes processed  */
  unsigned long state[5];     /*!< intermediate digest state  */
  unsigned char buffer[64];   /*!< data block being processed */
} sha1_context;

/*
 * SHA-1 context setup
 *
 * SHA-1 context to be initialized
 */
void sha1_starts( sha1_context *ctx );
void init_sha1_starts( sha1_context *ctx );

/*
 * SHA-1 process buffer
 *
 * SHA-1 context
 * buffer holding the  data
 * length of the input data
 */
void sha1_update( sha1_context *ctx,  const unsigned char *input, unsigned int ilen );
void init_sha1_update( sha1_context *ctx,  const unsigned char *input, unsigned int ilen );

/*
 * SHA-1 final digest
 * 
 * SHA-1 context
 * SHA-1 checksum result
 */
void sha1_finish( sha1_context *ctx, unsigned char output[SHA1_CHECKSUM_LEN] );
void init_sha1_finish( sha1_context *ctx, unsigned char output[SHA1_CHECKSUM_LEN] );
/*
 * Output = SHA-1( input buffer )
 *
 * buffer holding the  data
 * length of the input data
 * SHA-1 checksum result
 */
void sha1_csum(  const unsigned char *input, unsigned int ilen, unsigned char output[SHA1_CHECKSUM_LEN] );

#endif /* sha1.h */
