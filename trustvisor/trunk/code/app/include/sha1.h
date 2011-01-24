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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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
  unsigned char ipad[64];     /*!< HMAC: inner padding by yanlinl */
  unsigned char opad[64];     /*!< HMAC: outer padding by yanlinl */
} sha1_context;

/*
 * SHA-1 context setup
 *
 * SHA-1 context to be initialized
 */
void sha1_starts( sha1_context *ctx );

/*
 * SHA-1 process buffer
 *
 * SHA-1 context
 * buffer holding the  data
 * length of the input data
 */
void sha1_update( sha1_context *ctx,  unsigned char *input, u32 ilen );

/*
 * SHA-1 final digest
 * 
 * SHA-1 context
 * SHA-1 checksum result
 */
void sha1_finish( sha1_context *ctx, unsigned char output[SHA1_CHECKSUM_LEN] );

/*
 * Output = SHA-1( input buffer )
 *
 * buffer holding the  data
 * length of the input data
 * SHA-1 checksum result
 */
void sha1_csum(  unsigned char *input, u32 ilen, unsigned char output[SHA1_CHECKSUM_LEN] );

/* HMAC functions, add by yanlin at March 3 2009 */
/**                                                                                                                                                                    
 * \brief          SHA-1 HMAC context setup                                                                                                                            
 *                                                                                                                                                                     
 * \param ctx      HMAC context to be initialized                                                                                                                      
 * \param key      HMAC secret key                                                                                                                                     
 * \param keylen   length of the HMAC key                                                                                                                              
 */
void sha1_hmac_starts( sha1_context *ctx,
                       unsigned char *key, unsigned int keylen );

/**                                                                                                                                                                    
 * \brief          SHA-1 HMAC process buffer                                                                                                                           
 *                                                                                                                                                                     
 * \param ctx      HMAC context                                                                                                                                        
 * \param input    buffer holding the  data                                                                                                                            
 * \param ilen     length of the input data                                                                                                                            
 */
void sha1_hmac_update( sha1_context *ctx,
                       unsigned char *input, unsigned int ilen );

/**                                                                                                                                                                    
 * \brief          SHA-1 HMAC final digest                                                                                                                             
 *                                                                                                                                                                     
 * \param ctx      HMAC context                                                                                                                                        
 * \param output   SHA-1 HMAC checksum result                                                                                                                          
 */
void sha1_hmac_finish( sha1_context *ctx, unsigned char *output );

/**                                                                                                                                                                    
 * \brief          Output = HMAC-SHA-1( hmac key, input buffer )                                                                                                       
 *                                                                                                                                                                     
 * \param key      HMAC secret key                                                                                                                                     
 * \param keylen   length of the HMAC key                                                                                                                              
 * \param input    buffer holding the  data                                                                                                                            
 * \param ilen     length of the input data                                                                                                                            
 * \param output   HMAC-SHA-1 result                                                                                                                                   
 */
void sha1_hmac( unsigned char *key, unsigned int keylen,
                unsigned char *input, unsigned int ilen,
                unsigned char *output );


#endif /* sha1.h */
