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

#undef DESC_DEF_ONLY
#define LTC_SOURCE

#include <xmhf.h>
#include <xmhfcrypto.h>

/**
  Decode a SEQUENCE type using a VA list
  @param in    Input buffer
  @param inlen Length of input in octets
  @remark <...> is of the form <type, size, data> (int, unsigned long, void*)
  @return CRYPT_OK on success
*/  
int der_decode_sequence_multi(const unsigned char *in, unsigned long inlen, ...)
{
   int           err, type;
   unsigned long size, x;
   void          *data;
   va_list       args;
   ltc_asn1_list *list;

   LTC_ARGCHK(in    != NULL);

   /* get size of output that will be required */
   va_start(args, inlen);
   x = 0;
   for (;;) {
       type = va_arg(args, int);
       size = va_arg(args, unsigned long);
       data = va_arg(args, void*);

       if (type == LTC_ASN1_EOL) { 
          break;
       }

       switch (type) {
           case LTC_ASN1_BOOLEAN:
           case LTC_ASN1_INTEGER:
           case LTC_ASN1_SHORT_INTEGER:
           case LTC_ASN1_BIT_STRING:
           case LTC_ASN1_OCTET_STRING:
           case LTC_ASN1_NULL:
           case LTC_ASN1_OBJECT_IDENTIFIER:
           case LTC_ASN1_IA5_STRING:
           case LTC_ASN1_PRINTABLE_STRING:
           case LTC_ASN1_UTF8_STRING:
           case LTC_ASN1_UTCTIME:
           case LTC_ASN1_SET:
           case LTC_ASN1_SETOF:
           case LTC_ASN1_SEQUENCE:
           case LTC_ASN1_CHOICE:
                ++x; 
                break;
          
           default:
               va_end(args);
               return CRYPT_INVALID_ARG;
       }
   }
   va_end(args);

   /* allocate structure for x elements */
   if (x == 0) {
      return CRYPT_NOP;
   }

   list = XCALLOC(sizeof(*list), x);
   if (list == NULL) {
      return CRYPT_MEM;
   }

   /* fill in the structure */
   va_start(args, inlen);
   x = 0;
   for (;;) {
       type = va_arg(args, int);
       size = va_arg(args, unsigned long);
       data = va_arg(args, void*);

       if (type == LTC_ASN1_EOL) { 
          break;
       }

       switch (type) {
           case LTC_ASN1_BOOLEAN:
           case LTC_ASN1_INTEGER:
           case LTC_ASN1_SHORT_INTEGER:
           case LTC_ASN1_BIT_STRING:
           case LTC_ASN1_OCTET_STRING:
           case LTC_ASN1_NULL:
           case LTC_ASN1_OBJECT_IDENTIFIER:
           case LTC_ASN1_IA5_STRING:
           case LTC_ASN1_PRINTABLE_STRING:
           case LTC_ASN1_UTF8_STRING:
           case LTC_ASN1_UTCTIME:
           case LTC_ASN1_SEQUENCE:
           case LTC_ASN1_SET:
           case LTC_ASN1_SETOF:          
           case LTC_ASN1_CHOICE:
                list[x].type   = type;
                list[x].size   = size;
                list[x++].data = data;
                break;
         
           default:
               va_end(args);
               err = CRYPT_INVALID_ARG;
               goto LBL_ERR;
       }
   }
   va_end(args);

   err = der_decode_sequence(in, inlen, list, x);
LBL_ERR:
   XFREE(list);
   return err;
}


/**
  Encode a SEQUENCE type using a VA list
  @param out    [out] Destination for data
  @param outlen [in/out] Length of buffer and resulting length of output
  @remark <...> is of the form <type, size, data> (int, unsigned long, void*)
  @return CRYPT_OK on success
*/  
int der_encode_sequence_multi(unsigned char *out, unsigned long *outlen, ...)
{
   int           err, type;
   unsigned long size, x;
   void          *data;
   va_list       args;
   ltc_asn1_list *list;

   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* get size of output that will be required */
   va_start(args, outlen);
   x = 0;
   for (;;) {
       type = va_arg(args, int);
       size = va_arg(args, unsigned long);
       data = va_arg(args, void*);

       if (type == LTC_ASN1_EOL) { 
          break;
       }

       switch (type) {
           case LTC_ASN1_BOOLEAN:
           case LTC_ASN1_INTEGER:
           case LTC_ASN1_SHORT_INTEGER:
           case LTC_ASN1_BIT_STRING:
           case LTC_ASN1_OCTET_STRING:
           case LTC_ASN1_NULL:
           case LTC_ASN1_OBJECT_IDENTIFIER:
           case LTC_ASN1_IA5_STRING:
           case LTC_ASN1_PRINTABLE_STRING:
           case LTC_ASN1_UTF8_STRING:
           case LTC_ASN1_UTCTIME:
           case LTC_ASN1_SEQUENCE:
           case LTC_ASN1_SET:
           case LTC_ASN1_SETOF:
                ++x; 
                break;
          
           default:
               va_end(args);
               return CRYPT_INVALID_ARG;
       }
   }
   va_end(args);

   /* allocate structure for x elements */
   if (x == 0) {
      return CRYPT_NOP;
   }

   list = XCALLOC(sizeof(*list), x);
   if (list == NULL) {
      return CRYPT_MEM;
   }

   /* fill in the structure */
   va_start(args, outlen);
   x = 0;
   for (;;) {
       type = va_arg(args, int);
       size = va_arg(args, unsigned long);
       data = va_arg(args, void*);

       if (type == LTC_ASN1_EOL) { 
          break;
       }

       switch (type) {
           case LTC_ASN1_BOOLEAN:
           case LTC_ASN1_INTEGER:
           case LTC_ASN1_SHORT_INTEGER:
           case LTC_ASN1_BIT_STRING:
           case LTC_ASN1_OCTET_STRING:
           case LTC_ASN1_NULL:
           case LTC_ASN1_OBJECT_IDENTIFIER:
           case LTC_ASN1_IA5_STRING:
           case LTC_ASN1_PRINTABLE_STRING:
           case LTC_ASN1_UTF8_STRING:
           case LTC_ASN1_UTCTIME:
           case LTC_ASN1_SEQUENCE:
           case LTC_ASN1_SET:
           case LTC_ASN1_SETOF:
                list[x].type   = type;
                list[x].size   = size;
                list[x++].data = data;
                break;
         
           default:
               va_end(args);
               err = CRYPT_INVALID_ARG;
               goto LBL_ERR;
       }
   }
   va_end(args);

   err = der_encode_sequence(list, x, out, outlen);   
LBL_ERR:
   XFREE(list);
   return err;
}

/**
   Encode a SEQUENCE
   @param list      The list of items to encode
   @param inlen     The number of items in the list
   @param out       [out] The destination 
   @param outlen    [in/out] The size of the output
   @param type_of   LTC_ASN1_SEQUENCE or LTC_ASN1_SET/LTC_ASN1_SETOF
   @return CRYPT_OK on success
*/
int der_encode_sequence_ex(ltc_asn1_list *list, unsigned long inlen,
                           unsigned char *out,  unsigned long *outlen, int type_of) 
{
   int           err, type;
   unsigned long size, x, y, z, i;
   void          *data;

   LTC_ARGCHK(list    != NULL);
   LTC_ARGCHK(out     != NULL);
   LTC_ARGCHK(outlen  != NULL);

   /* get size of output that will be required */
   y = 0;
   for (i = 0; i < inlen; i++) {
       type = list[i].type;
       size = list[i].size;
       data = list[i].data;

       if (type == LTC_ASN1_EOL) { 
          break;
       }

       switch (type) {
            case LTC_ASN1_BOOLEAN:
               if ((err = der_length_boolean(&x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_INTEGER:
               if ((err = der_length_integer(data, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_SHORT_INTEGER:
               if ((err = der_length_short_integer(*((unsigned long*)data), &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_BIT_STRING:
               if ((err = der_length_bit_string(size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_OCTET_STRING:
               if ((err = der_length_octet_string(size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_NULL:
               y += 2;
               break;

           case LTC_ASN1_OBJECT_IDENTIFIER:
               if ((err = der_length_object_identifier(data, size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_IA5_STRING:
               if ((err = der_length_ia5_string(data, size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_PRINTABLE_STRING:
               if ((err = der_length_printable_string(data, size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_UTF8_STRING:
               if ((err = der_length_utf8_string(data, size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_UTCTIME:
               if ((err = der_length_utctime(data, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_SET:
           case LTC_ASN1_SETOF:
           case LTC_ASN1_SEQUENCE:
               if ((err = der_length_sequence(data, size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;
          
           default:
               err = CRYPT_INVALID_ARG;
               goto LBL_ERR;
       }
   }

   /* calc header size */
   z = y;
   if (y < 128) {
      y += 2;
   } else if (y < 256) {
      /* 0x30 0x81 LL */
      y += 3;
   } else if (y < 65536UL) {
      /* 0x30 0x82 LL LL */
      y += 4;
   } else if (y < 16777216UL) {
      /* 0x30 0x83 LL LL LL */
      y += 5;
   } else {
      err = CRYPT_INVALID_ARG;
      goto LBL_ERR;
   }

   /* too big ? */
   if (*outlen < y) {
      *outlen = y;
      err = CRYPT_BUFFER_OVERFLOW;
      goto LBL_ERR;
   }

   /* store header */
   x = 0;
   out[x++] = (type_of == LTC_ASN1_SEQUENCE) ? 0x30 : 0x31;
      
   if (z < 128) {
      out[x++] = (unsigned char)z;
   } else if (z < 256) {
      out[x++] = 0x81;
      out[x++] = (unsigned char)z;
   } else if (z < 65536UL) {
      out[x++] = 0x82;
      out[x++] = (unsigned char)((z>>8UL)&255);
      out[x++] = (unsigned char)(z&255);
   } else if (z < 16777216UL) {
      out[x++] = 0x83;
      out[x++] = (unsigned char)((z>>16UL)&255);
      out[x++] = (unsigned char)((z>>8UL)&255);
      out[x++] = (unsigned char)(z&255);
   }

   /* store data */
   *outlen -= x;
   for (i = 0; i < inlen; i++) {
       type = list[i].type;
       size = list[i].size;
       data = list[i].data;

       if (type == LTC_ASN1_EOL) { 
          break;
       }

       switch (type) {
            case LTC_ASN1_BOOLEAN:
               z = *outlen;
               if ((err = der_encode_boolean(*((int *)data), out + x, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;
          
           case LTC_ASN1_INTEGER:
               z = *outlen;
               if ((err = der_encode_integer(data, out + x, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;

           case LTC_ASN1_SHORT_INTEGER:
               z = *outlen;
               if ((err = der_encode_short_integer(*((unsigned long*)data), out + x, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;

           case LTC_ASN1_BIT_STRING:
               z = *outlen;
               if ((err = der_encode_bit_string(data, size, out + x, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;

           case LTC_ASN1_OCTET_STRING:
               z = *outlen;
               if ((err = der_encode_octet_string(data, size, out + x, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;

           case LTC_ASN1_NULL:
               out[x++] = 0x05;
               out[x++] = 0x00;
               *outlen -= 2;
               break;

           case LTC_ASN1_OBJECT_IDENTIFIER:
               z = *outlen;
               if ((err = der_encode_object_identifier(data, size, out + x, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;

           case LTC_ASN1_IA5_STRING:
               z = *outlen;
               if ((err = der_encode_ia5_string(data, size, out + x, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;
          
           case LTC_ASN1_PRINTABLE_STRING:
               z = *outlen;
               if ((err = der_encode_printable_string(data, size, out + x, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;

           case LTC_ASN1_UTF8_STRING:
               z = *outlen;
               if ((err = der_encode_utf8_string(data, size, out + x, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;

           case LTC_ASN1_UTCTIME:
               z = *outlen;
               if ((err = der_encode_utctime(data, out + x, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;

           case LTC_ASN1_SET:
               z = *outlen;
               if ((err = der_encode_set(data, size, out + x, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;

           case LTC_ASN1_SETOF:
               z = *outlen;
               if ((err = der_encode_setof(data, size, out + x, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;

           case LTC_ASN1_SEQUENCE:
               z = *outlen;
               if ((err = der_encode_sequence_ex(data, size, out + x, &z, type)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               x       += z;
               *outlen -= z;
               break;
           
           default:
               err = CRYPT_INVALID_ARG;
               goto LBL_ERR;
       }
   }
   *outlen = x;
   err = CRYPT_OK;   

LBL_ERR:
   return err;
}

/**
   Decode a SEQUENCE
   @param in       The DER encoded input
   @param inlen    The size of the input
   @param list     The list of items to decode
   @param outlen   The number of items in the list
   @param ordered  Search an unordeded or ordered list
   @return CRYPT_OK on success
*/
int der_decode_sequence_ex(const unsigned char *in, unsigned long  inlen,
                           ltc_asn1_list *list,     unsigned long  outlen, int ordered)
{
   int           err, type;
   unsigned long size, x, y, z, i, blksize;
   void          *data;

   LTC_ARGCHK(in   != NULL);
   LTC_ARGCHK(list != NULL);
   
   /* get blk size */
   if (inlen < 2) {
      return CRYPT_INVALID_PACKET;
   }

   /* sequence type? We allow 0x30 SEQUENCE and 0x31 SET since fundamentally they're the same structure */
   x = 0;
   if (in[x] != 0x30 && in[x] != 0x31) {
      return CRYPT_INVALID_PACKET;
   }
   ++x;

   if (in[x] < 128) {
      blksize = in[x++];
   } else if (in[x] & 0x80) {
      if (in[x] < 0x81 || in[x] > 0x83) {
         return CRYPT_INVALID_PACKET;
      }
      y = in[x++] & 0x7F;

      /* would reading the len bytes overrun? */
      if (x + y > inlen) {
         return CRYPT_INVALID_PACKET;
      }

      /* read len */
      blksize = 0;
      while (y--) {
          blksize = (blksize << 8) | (unsigned long)in[x++];
      }
  }

  /* would this blksize overflow? */
  if (x + blksize > inlen) {
     return CRYPT_INVALID_PACKET;
  }

   /* mark all as unused */
   for (i = 0; i < outlen; i++) {
       list[i].used = 0;
   }     

  /* ok read data */
   inlen = blksize;
   for (i = 0; i < outlen; i++) {
       z    = 0;
       type = list[i].type;
       size = list[i].size;
       data = list[i].data;
       if (!ordered && list[i].used == 1) { continue; }

       if (type == LTC_ASN1_EOL) { 
          break;
       }

       switch (type) {
           case LTC_ASN1_BOOLEAN:
               z = inlen;
               if ((err = der_decode_boolean(in + x, z, ((int *)data))) != CRYPT_OK) {
                   goto LBL_ERR;
               }
               if ((err = der_length_boolean(&z)) != CRYPT_OK) {
                   goto LBL_ERR;
                }
                break;
          
           case LTC_ASN1_INTEGER:
               z = inlen;
               if ((err = der_decode_integer(in + x, z, data)) != CRYPT_OK) {
                  if (!ordered) {  continue; }
                  goto LBL_ERR;
               }
               if ((err = der_length_integer(data, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               break;

           case LTC_ASN1_SHORT_INTEGER:
               z = inlen;
               if ((err = der_decode_short_integer(in + x, z, data)) != CRYPT_OK) {
                  if (!ordered) { continue; }
                  goto LBL_ERR;
               }
               if ((err = der_length_short_integer(((unsigned long*)data)[0], &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               
               break;

           case LTC_ASN1_BIT_STRING:
               z = inlen;
               if ((err = der_decode_bit_string(in + x, z, data, &size)) != CRYPT_OK) {
                  if (!ordered) { continue; }
                  goto LBL_ERR;
               }
               list[i].size = size;
               if ((err = der_length_bit_string(size, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               break;

           case LTC_ASN1_OCTET_STRING:
               z = inlen;
               if ((err = der_decode_octet_string(in + x, z, data, &size)) != CRYPT_OK) {
                  if (!ordered) { continue; }
                  goto LBL_ERR;
               }
               list[i].size = size;
               if ((err = der_length_octet_string(size, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               break;

           case LTC_ASN1_NULL:
               if (inlen < 2 || in[x] != 0x05 || in[x+1] != 0x00) {
                  if (!ordered) { continue; }
                  err = CRYPT_INVALID_PACKET;
                  goto LBL_ERR;
               }
               z = 2;
               break;
                  
           case LTC_ASN1_OBJECT_IDENTIFIER:
               z = inlen;
               if ((err = der_decode_object_identifier(in + x, z, data, &size)) != CRYPT_OK) {
                  if (!ordered) { continue; }
                  goto LBL_ERR;
               }
               list[i].size = size;
               if ((err = der_length_object_identifier(data, size, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               break;

           case LTC_ASN1_IA5_STRING:
               z = inlen;
               if ((err = der_decode_ia5_string(in + x, z, data, &size)) != CRYPT_OK) {
                  if (!ordered) { continue; }
                  goto LBL_ERR;
               }
               list[i].size = size;
               if ((err = der_length_ia5_string(data, size, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               break;


           case LTC_ASN1_PRINTABLE_STRING:
               z = inlen;
               if ((err = der_decode_printable_string(in + x, z, data, &size)) != CRYPT_OK) {
                  if (!ordered) { continue; }
                  goto LBL_ERR;
               }
               list[i].size = size;
               if ((err = der_length_printable_string(data, size, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               break;

           case LTC_ASN1_UTF8_STRING:
               z = inlen;
               if ((err = der_decode_utf8_string(in + x, z, data, &size)) != CRYPT_OK) {
                  if (!ordered) { continue; }
                  goto LBL_ERR;
               }
               list[i].size = size;
               if ((err = der_length_utf8_string(data, size, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               break;

           case LTC_ASN1_UTCTIME:
               z = inlen;
               if ((err = der_decode_utctime(in + x, &z, data)) != CRYPT_OK) {
                  if (!ordered) { continue; }
                  goto LBL_ERR;
               }
               break;

           case LTC_ASN1_SET:
               z = inlen;
               if ((err = der_decode_set(in + x, z, data, size)) != CRYPT_OK) {
                  if (!ordered) { continue; }
                  goto LBL_ERR;
               }
               if ((err = der_length_sequence(data, size, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               break;
           
           case LTC_ASN1_SETOF:
           case LTC_ASN1_SEQUENCE:
               /* detect if we have the right type */
               if ((type == LTC_ASN1_SETOF && (in[x] & 0x3F) != 0x31) || (type == LTC_ASN1_SEQUENCE && (in[x] & 0x3F) != 0x30)) {
                  err = CRYPT_INVALID_PACKET;
                  goto LBL_ERR;
               }

               z = inlen;
               if ((err = der_decode_sequence(in + x, z, data, size)) != CRYPT_OK) {
                  if (!ordered) { continue; }
                  goto LBL_ERR;
               }
               if ((err = der_length_sequence(data, size, &z)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               break;


           case LTC_ASN1_CHOICE:
               z = inlen;
               if ((err = der_decode_choice(in + x, &z, data, size)) != CRYPT_OK) {
                  if (!ordered) { continue; }
                  goto LBL_ERR;
               }
               break;

           default:
               err = CRYPT_INVALID_ARG;
               goto LBL_ERR;
       }
       x           += z;
       inlen       -= z;
       list[i].used = 1;
       if (!ordered) { 
          /* restart the decoder */
          i = -1;
       }          
   }
     
   for (i = 0; i < outlen; i++) {
      if (list[i].used == 0) {
          err = CRYPT_INVALID_PACKET;
          goto LBL_ERR;
      }
   }                
   err = CRYPT_OK;   

LBL_ERR:
   return err;
}  

/**
   Get the length of a DER sequence 
   @param list   The sequences of items in the SEQUENCE
   @param inlen  The number of items
   @param outlen [out] The length required in octets to store it 
   @return CRYPT_OK on success
*/
int der_length_sequence(ltc_asn1_list *list, unsigned long inlen,
                        unsigned long *outlen) 
{
   int           err, type;
   unsigned long size, x, y, z, i;
   void          *data;

   LTC_ARGCHK(list    != NULL);
   LTC_ARGCHK(outlen  != NULL);

   /* get size of output that will be required */
   y = 0;
   for (i = 0; i < inlen; i++) {
       type = list[i].type;
       size = list[i].size;
       data = list[i].data;

       if (type == LTC_ASN1_EOL) { 
          break;
       }

       switch (type) {
           case LTC_ASN1_BOOLEAN:
              if ((err = der_length_boolean(&x)) != CRYPT_OK) {
                 goto LBL_ERR;
              }
              y += x;
              break;
          
           case LTC_ASN1_INTEGER:
               if ((err = der_length_integer(data, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_SHORT_INTEGER:
               if ((err = der_length_short_integer(*((unsigned long *)data), &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_BIT_STRING:
               if ((err = der_length_bit_string(size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_OCTET_STRING:
               if ((err = der_length_octet_string(size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_NULL:
               y += 2;
               break;

           case LTC_ASN1_OBJECT_IDENTIFIER:
               if ((err = der_length_object_identifier(data, size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_IA5_STRING:
               if ((err = der_length_ia5_string(data, size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_PRINTABLE_STRING:
               if ((err = der_length_printable_string(data, size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_UTCTIME:
               if ((err = der_length_utctime(data, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_UTF8_STRING:
               if ((err = der_length_utf8_string(data, size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

           case LTC_ASN1_SET:
           case LTC_ASN1_SETOF:
           case LTC_ASN1_SEQUENCE:
               if ((err = der_length_sequence(data, size, &x)) != CRYPT_OK) {
                  goto LBL_ERR;
               }
               y += x;
               break;

          
           default:
               err = CRYPT_INVALID_ARG;
               goto LBL_ERR;
       }
   }

   /* calc header size */
   z = y;
   if (y < 128) {
      y += 2;
   } else if (y < 256) {
      /* 0x30 0x81 LL */
      y += 3;
   } else if (y < 65536UL) {
      /* 0x30 0x82 LL LL */
      y += 4;
   } else if (y < 16777216UL) {
      /* 0x30 0x83 LL LL LL */
      y += 5;
   } else {
      err = CRYPT_INVALID_ARG;
      goto LBL_ERR;
   }

   /* store size */
   *outlen = y;
   err     = CRYPT_OK;

LBL_ERR:
   return err;
}



/*
 * BIT
 */

/**
  Store a BIT STRING
  @param in      The DER encoded BIT STRING
  @param inlen   The size of the DER BIT STRING
  @param out     [out] The array of bits stored (one per char)
  @param outlen  [in/out] The number of bits stored
  @return CRYPT_OK if successful
*/
int der_decode_bit_string(const unsigned char *in,  unsigned long inlen,
                                unsigned char *out, unsigned long *outlen)
{
   unsigned long dlen, blen, x, y;

   LTC_ARGCHK(in     != NULL);
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* packet must be at least 4 bytes */
   if (inlen < 4) {
       return CRYPT_INVALID_ARG;
   }

   /* check for 0x03 */
   if ((in[0]&0x1F) != 0x03) {
      return CRYPT_INVALID_PACKET;
   }

    /* offset in the data */
    x = 1;

   /* get the length of the data */
   if (in[x] & 0x80) {
      /* long format get number of length bytes */
      y = in[x++] & 0x7F;

      /* invalid if 0 or > 2 */
      if (y == 0 || y > 2) {
         return CRYPT_INVALID_PACKET;
      }

      /* read the data len */
      dlen = 0;
      while (y--) {
         dlen = (dlen << 8) | (unsigned long)in[x++];
      }
   } else {
      /* short format */
      dlen = in[x++] & 0x7F;
   }
  
   /* is the data len too long or too short? */
   if ((dlen == 0) || (dlen + x > inlen)) {
       return CRYPT_INVALID_PACKET;
   }

   /* get padding count */
   blen = ((dlen - 1) << 3) - (in[x++] & 7);

   /* too many bits? */
   if (blen > *outlen) {
      *outlen = blen;
      return CRYPT_BUFFER_OVERFLOW;
   }

   /* decode/store the bits */
   for (y = 0; y < blen; y++) {
       out[y] = (in[x] & (1 << (7 - (y & 7)))) ? 1 : 0;
       if ((y & 7) == 7) {
          ++x;
       }
   }

   /* we done */
   *outlen = blen;
   return CRYPT_OK;
}

/**
  Store a BIT STRING
  @param in       The array of bits to store (one per char)
  @param inlen    The number of bits tostore
  @param out      [out] The destination for the DER encoded BIT STRING
  @param outlen   [in/out] The max size and resulting size of the DER BIT STRING
  @return CRYPT_OK if successful
*/
int der_encode_bit_string(const unsigned char *in, unsigned long inlen,
                                unsigned char *out, unsigned long *outlen)
{
   unsigned long len, x, y;
   unsigned char buf;
   int           err;

   LTC_ARGCHK(in     != NULL);
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* avoid overflows */
   if ((err = der_length_bit_string(inlen, &len)) != CRYPT_OK) {
      return err;
   }

   if (len > *outlen) {
      *outlen = len;
      return CRYPT_BUFFER_OVERFLOW;
   }

   /* store header (include bit padding count in length) */
   x = 0;
   y = (inlen >> 3) + ((inlen&7) ? 1 : 0) + 1;

   out[x++] = 0x03;
   if (y < 128) {
      out[x++] = (unsigned char)y;
   } else if (y < 256) {
      out[x++] = 0x81;
      out[x++] = (unsigned char)y;
   } else if (y < 65536) {
      out[x++] = 0x82;
      out[x++] = (unsigned char)((y>>8)&255);
      out[x++] = (unsigned char)(y&255);
   }

   /* store number of zero padding bits */
   out[x++] = (unsigned char)((8 - inlen) & 7);

   /* store the bits in big endian format */
   for (y = buf = 0; y < inlen; y++) {
       buf |= (in[y] ? 1 : 0) << (7 - (y & 7));
       if ((y & 7) == 7) {
          out[x++] = buf;
          buf      = 0;
       }
   }
   /* store last byte */
   if (inlen & 7) {
      out[x++] = buf;
   }
   *outlen = x;
   return CRYPT_OK;
}

/**
  Gets length of DER encoding of BIT STRING 
  @param nbits  The number of bits in the string to encode
  @param outlen [out] The length of the DER encoding for the given string
  @return CRYPT_OK if successful
*/
int der_length_bit_string(unsigned long nbits, unsigned long *outlen)
{
   unsigned long nbytes;
   LTC_ARGCHK(outlen != NULL);

   /* get the number of the bytes */
   nbytes = (nbits >> 3) + ((nbits & 7) ? 1 : 0) + 1;
 
   if (nbytes < 128) {
      /* 03 LL PP DD DD DD ... */
      *outlen = 2 + nbytes;
   } else if (nbytes < 256) {
      /* 03 81 LL PP DD DD DD ... */
      *outlen = 3 + nbytes;
   } else if (nbytes < 65536) {
      /* 03 82 LL LL PP DD DD DD ... */
      *outlen = 4 + nbytes;
   } else {
      return CRYPT_INVALID_ARG;
   }

   return CRYPT_OK;
}

/*
 * BOOLEAN
 */

/**
  Read a BOOLEAN
  @param in      The destination for the DER encoded BOOLEAN
  @param inlen   The size of the DER BOOLEAN
  @param out     [out]  The boolean to decode
  @return CRYPT_OK if successful
*/
int der_decode_boolean(const unsigned char *in, unsigned long inlen,
                                       int *out)
{
   LTC_ARGCHK(in  != NULL);
   LTC_ARGCHK(out != NULL);
   
   if (inlen != 3 || in[0] != 0x01 || in[1] != 0x01 || (in[2] != 0x00 && in[2] != 0xFF)) {
      return CRYPT_INVALID_ARG;
   }
   
   *out = (in[2]==0xFF) ? 1 : 0;
   
   return CRYPT_OK;
}

/**
  Store a BOOLEAN
  @param in       The boolean to encode
  @param out      [out] The destination for the DER encoded BOOLEAN
  @param outlen   [in/out] The max size and resulting size of the DER BOOLEAN
  @return CRYPT_OK if successful
*/
int der_encode_boolean(int in, 
                       unsigned char *out, unsigned long *outlen)
{
   LTC_ARGCHK(outlen != NULL);
   LTC_ARGCHK(out    != NULL);
   
   if (*outlen < 3) {
       *outlen = 3;
       return CRYPT_BUFFER_OVERFLOW;
   }
   
   *outlen = 3;
   out[0] = 0x01;
   out[1] = 0x01;
   out[2] = in ? 0xFF : 0x00;
   
   return CRYPT_OK;
}

/**
  Gets length of DER encoding of a BOOLEAN 
  @param outlen [out] The length of the DER encoding
  @return CRYPT_OK if successful
*/
int der_length_boolean(unsigned long *outlen)
{
   LTC_ARGCHK(outlen != NULL);
   *outlen = 3;
   return CRYPT_OK;
}

/*
 * CHOICE
 */

/**
   Decode a CHOICE
   @param in       The DER encoded input
   @param inlen    [in/out] The size of the input and resulting size of read type
   @param list     The list of items to decode
   @param outlen   The number of items in the list
   @return CRYPT_OK on success
*/
int der_decode_choice(const unsigned char *in,   unsigned long *inlen,
                            ltc_asn1_list *list, unsigned long  outlen)
{
   unsigned long size, x, z;
   void          *data;

   LTC_ARGCHK(in    != NULL);
   LTC_ARGCHK(inlen != NULL);
   LTC_ARGCHK(list  != NULL);

   /* get blk size */
   if (*inlen < 2) {
      return CRYPT_INVALID_PACKET;
   }

   /* set all of the "used" flags to zero */
   for (x = 0; x < outlen; x++) {
       list[x].used = 0;
   }

   /* now scan until we have a winner */
   for (x = 0; x < outlen; x++) {
       size = list[x].size;
       data = list[x].data;

       switch (list[x].type) {
           case LTC_ASN1_INTEGER:
               if (der_decode_integer(in, *inlen, data) == CRYPT_OK) {
                  if (der_length_integer(data, &z) == CRYPT_OK) {
                      list[x].used = 1;
                      *inlen       = z;
                      return CRYPT_OK;
                  }
               }
               break;

           case LTC_ASN1_SHORT_INTEGER:
               if (der_decode_short_integer(in, *inlen, data) == CRYPT_OK) {
                  if (der_length_short_integer(size, &z) == CRYPT_OK) {
                      list[x].used = 1;
                      *inlen       = z;
                      return CRYPT_OK;
                  }
               }
               break;

           case LTC_ASN1_BIT_STRING:
               if (der_decode_bit_string(in, *inlen, data, &size) == CRYPT_OK) {
                  if (der_length_bit_string(size, &z) == CRYPT_OK) {
                     list[x].used = 1;
                     list[x].size = size;
                     *inlen       = z;
                     return CRYPT_OK;
                  }
               }
               break;

           case LTC_ASN1_OCTET_STRING:
               if (der_decode_octet_string(in, *inlen, data, &size) == CRYPT_OK) {
                  if (der_length_octet_string(size, &z) == CRYPT_OK) {
                     list[x].used = 1;
                     list[x].size = size;
                     *inlen       = z;
                     return CRYPT_OK;
                  }
               }
               break;

           case LTC_ASN1_NULL:
               if (*inlen == 2 && in[x] == 0x05 && in[x+1] == 0x00) {
                  *inlen = 2;
                  list[x].used   = 1;
                  return CRYPT_OK;
               }
               break;
                  
           case LTC_ASN1_OBJECT_IDENTIFIER:
               if (der_decode_object_identifier(in, *inlen, data, &size) == CRYPT_OK) {
                  if (der_length_object_identifier(data, size, &z) == CRYPT_OK) {
                     list[x].used = 1;
                     list[x].size = size;
                     *inlen       = z;
                     return CRYPT_OK;
                  }
               }
               break;

           case LTC_ASN1_IA5_STRING:
               if (der_decode_ia5_string(in, *inlen, data, &size) == CRYPT_OK) {
                  if (der_length_ia5_string(data, size, &z) == CRYPT_OK) {
                     list[x].used = 1;
                     list[x].size = size;
                     *inlen       = z;
                     return CRYPT_OK;
                  }
               }
               break;


           case LTC_ASN1_PRINTABLE_STRING:
               if (der_decode_printable_string(in, *inlen, data, &size) == CRYPT_OK) {
                  if (der_length_printable_string(data, size, &z) == CRYPT_OK) {
                     list[x].used = 1;
                     list[x].size = size;
                     *inlen       = z;
                     return CRYPT_OK;
                  }
               }
               break;

           case LTC_ASN1_UTF8_STRING:
               if (der_decode_utf8_string(in, *inlen, data, &size) == CRYPT_OK) {
                  if (der_length_utf8_string(data, size, &z) == CRYPT_OK) {
                     list[x].used = 1;
                     list[x].size = size;
                     *inlen       = z;
                     return CRYPT_OK;
                  }
               }
               break;

           case LTC_ASN1_UTCTIME:
               z = *inlen;
               if (der_decode_utctime(in, &z, data) == CRYPT_OK) {
                  list[x].used = 1;
                  *inlen       = z;
                  return CRYPT_OK;
               }
               break;

           case LTC_ASN1_SET:
           case LTC_ASN1_SETOF:
           case LTC_ASN1_SEQUENCE:
               if (der_decode_sequence(in, *inlen, data, size) == CRYPT_OK) {
                  if (der_length_sequence(data, size, &z) == CRYPT_OK) {
                     list[x].used = 1;
                     *inlen       = z;
                     return CRYPT_OK;
                  }
               }
               break;

           default:
               return CRYPT_INVALID_ARG;
       }
   }

   return CRYPT_INVALID_PACKET;
}

/*
 * IA5
 */

/**
  Store a IA5 STRING
  @param in      The DER encoded IA5 STRING
  @param inlen   The size of the DER IA5 STRING
  @param out     [out] The array of octets stored (one per char)
  @param outlen  [in/out] The number of octets stored
  @return CRYPT_OK if successful
*/
int der_decode_ia5_string(const unsigned char *in, unsigned long inlen,
                                unsigned char *out, unsigned long *outlen)
{
   unsigned long x, y, len;
   int           t;

   LTC_ARGCHK(in     != NULL);
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* must have header at least */
   if (inlen < 2) {
      return CRYPT_INVALID_PACKET;
   }

   /* check for 0x16 */
   if ((in[0] & 0x1F) != 0x16) {
      return CRYPT_INVALID_PACKET;
   }
   x = 1;

   /* decode the length */
   if (in[x] & 0x80) {
      /* valid # of bytes in length are 1,2,3 */
      y = in[x] & 0x7F;
      if ((y == 0) || (y > 3) || ((x + y) > inlen)) {
         return CRYPT_INVALID_PACKET;
      }

      /* read the length in */
      len = 0;
      ++x;
      while (y--) {
         len = (len << 8) | in[x++];
      }
   } else {
      len = in[x++] & 0x7F;
   }

   /* is it too long? */
   if (len > *outlen) {
      *outlen = len;
      return CRYPT_BUFFER_OVERFLOW;
   }

   if (len + x > inlen) {
      return CRYPT_INVALID_PACKET;
   }

   /* read the data */
   for (y = 0; y < len; y++) {
       t = der_ia5_value_decode(in[x++]);
       if (t == -1) {
           return CRYPT_INVALID_ARG;
       }
       out[y] = t;
   }

   *outlen = y;

   return CRYPT_OK;
}

/**
  Store an IA5 STRING
  @param in       The array of IA5 to store (one per char)
  @param inlen    The number of IA5 to store
  @param out      [out] The destination for the DER encoded IA5 STRING
  @param outlen   [in/out] The max size and resulting size of the DER IA5 STRING
  @return CRYPT_OK if successful
*/
int der_encode_ia5_string(const unsigned char *in, unsigned long inlen,
                                unsigned char *out, unsigned long *outlen)
{
   unsigned long x, y, len;
   int           err;

   LTC_ARGCHK(in     != NULL);
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* get the size */
   if ((err = der_length_ia5_string(in, inlen, &len)) != CRYPT_OK) {
      return err; 
   }

   /* too big? */
   if (len > *outlen) {
      *outlen = len;
      return CRYPT_BUFFER_OVERFLOW;
   }

   /* encode the header+len */
   x = 0;
   out[x++] = 0x16;
   if (inlen < 128) {
      out[x++] = (unsigned char)inlen;
   } else if (inlen < 256) {
      out[x++] = 0x81;
      out[x++] = (unsigned char)inlen;
   } else if (inlen < 65536UL) {
      out[x++] = 0x82;
      out[x++] = (unsigned char)((inlen>>8)&255);
      out[x++] = (unsigned char)(inlen&255);
   } else if (inlen < 16777216UL) {
      out[x++] = 0x83;
      out[x++] = (unsigned char)((inlen>>16)&255);
      out[x++] = (unsigned char)((inlen>>8)&255);
      out[x++] = (unsigned char)(inlen&255);
   } else {
      return CRYPT_INVALID_ARG;
   }

   /* store octets */
   for (y = 0; y < inlen; y++) {
       out[x++] = der_ia5_char_encode(in[y]);
   }

   /* retun length */
   *outlen = x;

   return CRYPT_OK;
}

static const struct {
   int code, value;
} ia5_table[] = {
{ '\0', 0 },
{ '\a', 7 }, 
{ '\b', 8 }, 
{ '\t', 9 }, 
{ '\n', 10 }, 
{ '\f', 12 }, 
{ '\r', 13 }, 
{ ' ', 32 }, 
{ '!', 33 }, 
{ '"', 34 }, 
{ '#', 35 }, 
{ '$', 36 }, 
{ '%', 37 }, 
{ '&', 38 }, 
{ '\'', 39 }, 
{ '(', 40 }, 
{ ')', 41 }, 
{ '*', 42 }, 
{ '+', 43 }, 
{ ',', 44 }, 
{ '-', 45 }, 
{ '.', 46 }, 
{ '/', 47 }, 
{ '0', 48 }, 
{ '1', 49 }, 
{ '2', 50 }, 
{ '3', 51 }, 
{ '4', 52 }, 
{ '5', 53 }, 
{ '6', 54 }, 
{ '7', 55 }, 
{ '8', 56 }, 
{ '9', 57 }, 
{ ':', 58 }, 
{ ';', 59 }, 
{ '<', 60 }, 
{ '=', 61 }, 
{ '>', 62 }, 
{ '?', 63 }, 
{ '@', 64 }, 
{ 'A', 65 }, 
{ 'B', 66 }, 
{ 'C', 67 }, 
{ 'D', 68 }, 
{ 'E', 69 }, 
{ 'F', 70 }, 
{ 'G', 71 }, 
{ 'H', 72 }, 
{ 'I', 73 }, 
{ 'J', 74 }, 
{ 'K', 75 }, 
{ 'L', 76 }, 
{ 'M', 77 }, 
{ 'N', 78 }, 
{ 'O', 79 }, 
{ 'P', 80 }, 
{ 'Q', 81 }, 
{ 'R', 82 }, 
{ 'S', 83 }, 
{ 'T', 84 }, 
{ 'U', 85 }, 
{ 'V', 86 }, 
{ 'W', 87 }, 
{ 'X', 88 }, 
{ 'Y', 89 }, 
{ 'Z', 90 }, 
{ '[', 91 }, 
{ '\\', 92 }, 
{ ']', 93 }, 
{ '^', 94 }, 
{ '_', 95 }, 
{ '`', 96 }, 
{ 'a', 97 }, 
{ 'b', 98 }, 
{ 'c', 99 }, 
{ 'd', 100 }, 
{ 'e', 101 }, 
{ 'f', 102 }, 
{ 'g', 103 }, 
{ 'h', 104 }, 
{ 'i', 105 }, 
{ 'j', 106 }, 
{ 'k', 107 }, 
{ 'l', 108 }, 
{ 'm', 109 }, 
{ 'n', 110 }, 
{ 'o', 111 }, 
{ 'p', 112 }, 
{ 'q', 113 }, 
{ 'r', 114 }, 
{ 's', 115 }, 
{ 't', 116 }, 
{ 'u', 117 }, 
{ 'v', 118 }, 
{ 'w', 119 }, 
{ 'x', 120 }, 
{ 'y', 121 }, 
{ 'z', 122 }, 
{ '{', 123 }, 
{ '|', 124 }, 
{ '}', 125 }, 
{ '~', 126 }
};

int der_ia5_char_encode(int c)
{
   int x;
   for (x = 0; x < (int)(sizeof(ia5_table)/sizeof(ia5_table[0])); x++) {
       if (ia5_table[x].code == c) {
          return ia5_table[x].value;
       }
   }
   return -1;
}

int der_ia5_value_decode(int v)
{
   int x;
   for (x = 0; x < (int)(sizeof(ia5_table)/sizeof(ia5_table[0])); x++) {
       if (ia5_table[x].value == v) {
          return ia5_table[x].code;
       }
   }
   return -1;
}
   
/**
  Gets length of DER encoding of IA5 STRING 
  @param octets   The values you want to encode 
  @param noctets  The number of octets in the string to encode
  @param outlen   [out] The length of the DER encoding for the given string
  @return CRYPT_OK if successful
*/
int der_length_ia5_string(const unsigned char *octets, unsigned long noctets, unsigned long *outlen)
{
   unsigned long x;

   LTC_ARGCHK(outlen != NULL);
   LTC_ARGCHK(octets != NULL);

   /* scan string for validity */
   for (x = 0; x < noctets; x++) {
       if (der_ia5_char_encode(octets[x]) == -1) {
          return CRYPT_INVALID_ARG;
       }
   }

   if (noctets < 128) {
      /* 16 LL DD DD DD ... */
      *outlen = 2 + noctets;
   } else if (noctets < 256) {
      /* 16 81 LL DD DD DD ... */
      *outlen = 3 + noctets;
   } else if (noctets < 65536UL) {
      /* 16 82 LL LL DD DD DD ... */
      *outlen = 4 + noctets;
   } else if (noctets < 16777216UL) {
      /* 16 83 LL LL LL DD DD DD ... */
      *outlen = 5 + noctets;
   } else {
      return CRYPT_INVALID_ARG;
   }

   return CRYPT_OK;
}

/*
 * INTEGER
 */

/**
  Read a mp_int integer
  @param in       The DER encoded data
  @param inlen    Size of DER encoded data
  @param num      The first mp_int to decode
  @return CRYPT_OK if successful
*/
int der_decode_integer(const unsigned char *in, unsigned long inlen, void *num)
{
   unsigned long x, y, z;
   int           err;

   LTC_ARGCHK(num    != NULL);
   LTC_ARGCHK(in     != NULL);

   /* min DER INTEGER is 0x02 01 00 == 0 */
   if (inlen < (1 + 1 + 1)) {
      return CRYPT_INVALID_PACKET;
   }

   /* ok expect 0x02 when we AND with 0001 1111 [1F] */
   x = 0;
   if ((in[x++] & 0x1F) != 0x02) {
      return CRYPT_INVALID_PACKET;
   }

   /* now decode the len stuff */
   z = in[x++];

   if ((z & 0x80) == 0x00) {
      /* short form */

      /* will it overflow? */
      if (x + z > inlen) {
         return CRYPT_INVALID_PACKET;
      }
     
      /* no so read it */
      if ((err = mp_read_unsigned_bin(num, (unsigned char *)in + x, z)) != CRYPT_OK) {
         return err;
      }
   } else {
      /* long form */
      z &= 0x7F;
      
      /* will number of length bytes overflow? (or > 4) */
      if (((x + z) > inlen) || (z > 4) || (z == 0)) {
         return CRYPT_INVALID_PACKET;
      }

      /* now read it in */
      y = 0;
      while (z--) {
         y = ((unsigned long)(in[x++])) | (y << 8);
      }

      /* now will reading y bytes overrun? */
      if ((x + y) > inlen) {
         return CRYPT_INVALID_PACKET;
      }

      /* no so read it */
      if ((err = mp_read_unsigned_bin(num, (unsigned char *)in + x, y)) != CRYPT_OK) {
         return err;
      }
   }

   /* see if it's negative */
   if (in[x] & 0x80) {
      void *tmp;
      if (mp_init(&tmp) != CRYPT_OK) {
         return CRYPT_MEM;
      }

      if (mp_2expt(tmp, mp_count_bits(num)) != CRYPT_OK || mp_sub(num, tmp, num) != CRYPT_OK) {
         mp_clear(tmp);
         return CRYPT_MEM;
      }
      mp_clear(tmp);
   } 

   return CRYPT_OK;

}

/* Exports a positive bignum as DER format (upto 2^32 bytes in size) */
/**
  Store a mp_int integer
  @param num      The first mp_int to encode
  @param out      [out] The destination for the DER encoded integers
  @param outlen   [in/out] The max size and resulting size of the DER encoded integers
  @return CRYPT_OK if successful
*/
int der_encode_integer(void *num, unsigned char *out, unsigned long *outlen)
{  
   unsigned long tmplen, y;
   int           err, leading_zero;

   LTC_ARGCHK(num    != NULL);
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* find out how big this will be */
   if ((err = der_length_integer(num, &tmplen)) != CRYPT_OK) {
      return err;
   }

   if (*outlen < tmplen) {
      *outlen = tmplen;
      return CRYPT_BUFFER_OVERFLOW;
   }

   if (mp_cmp_d(num, 0) != LTC_MP_LT) {
      /* we only need a leading zero if the msb of the first byte is one */
      if ((mp_count_bits(num) & 7) == 0 || mp_iszero(num) == LTC_MP_YES) {
         leading_zero = 1;
      } else {
         leading_zero = 0;
      }

      /* get length of num in bytes (plus 1 since we force the msbyte to zero) */
      y = mp_unsigned_bin_size(num) + leading_zero;
   } else {
      leading_zero = 0;
      y            = mp_count_bits(num);
      y            = y + (8 - (y & 7));
      y            = y >> 3;
      if (((mp_cnt_lsb(num)+1)==mp_count_bits(num)) && ((mp_count_bits(num)&7)==0)) --y;
   }

   /* now store initial data */
   *out++ = 0x02;
   if (y < 128) {
      /* short form */
      *out++ = (unsigned char)y;
   } else if (y < 256) {
      *out++ = 0x81;
      *out++ = (unsigned char)y;
   } else if (y < 65536UL) {
      *out++ = 0x82;
      *out++ = (unsigned char)((y>>8)&255);
      *out++ = (unsigned char)y;
   } else if (y < 16777216UL) {
      *out++ = 0x83;
      *out++ = (unsigned char)((y>>16)&255);
      *out++ = (unsigned char)((y>>8)&255);
      *out++ = (unsigned char)y;
   } else {
      return CRYPT_INVALID_ARG;
   }

   /* now store msbyte of zero if num is non-zero */
   if (leading_zero) {
      *out++ = 0x00;
   }

   /* if it's not zero store it as big endian */
   if (mp_cmp_d(num, 0) == LTC_MP_GT) {
      /* now store the mpint */
      if ((err = mp_to_unsigned_bin(num, out)) != CRYPT_OK) {
          return err;
      }
   } else if (mp_iszero(num) != LTC_MP_YES) {
      void *tmp;
         
      /* negative */
      if (mp_init(&tmp) != CRYPT_OK) {
         return CRYPT_MEM;
      }

      /* 2^roundup and subtract */
      y = mp_count_bits(num);
      y = y + (8 - (y & 7));
      if (((mp_cnt_lsb(num)+1)==mp_count_bits(num)) && ((mp_count_bits(num)&7)==0)) y -= 8;
      if (mp_2expt(tmp, y) != CRYPT_OK || mp_add(tmp, num, tmp) != CRYPT_OK) {
         mp_clear(tmp);
         return CRYPT_MEM;
      }
      if ((err = mp_to_unsigned_bin(tmp, out)) != CRYPT_OK) {
         mp_clear(tmp);
         return err;
      }
      mp_clear(tmp);
   }

   /* we good */
   *outlen = tmplen; 
   return CRYPT_OK;
}

/**
  Gets length of DER encoding of num 
  @param num    The int to get the size of 
  @param outlen [out] The length of the DER encoding for the given integer
  @return CRYPT_OK if successful
*/
int der_length_integer(void *num, unsigned long *outlen)
{
   unsigned long z, len;
   int           leading_zero;

   LTC_ARGCHK(num     != NULL);
   LTC_ARGCHK(outlen  != NULL);

   if (mp_cmp_d(num, 0) != LTC_MP_LT) {
      /* positive */

      /* we only need a leading zero if the msb of the first byte is one */
      if ((mp_count_bits(num) & 7) == 0 || mp_iszero(num) == LTC_MP_YES) {
         leading_zero = 1;
      } else {
         leading_zero = 0;
      }

      /* size for bignum */
      z = len = leading_zero + mp_unsigned_bin_size(num);
   } else {
      /* it's negative */
      /* find power of 2 that is a multiple of eight and greater than count bits */
      leading_zero = 0;
      z = mp_count_bits(num);
      z = z + (8 - (z & 7));
      if (((mp_cnt_lsb(num)+1)==mp_count_bits(num)) && ((mp_count_bits(num)&7)==0)) --z;
      len = z = z >> 3;
   }

   /* now we need a length */
   if (z < 128) {
      /* short form */
      ++len;
   } else {
      /* long form (relies on z != 0), assumes length bytes < 128 */
      ++len;

      while (z) {
         ++len;
         z >>= 8;
      }
   }

   /* we need a 0x02 to indicate it's INTEGER */
   ++len;

   /* return length */
   *outlen = len; 
   return CRYPT_OK;
}

/*
 * OBJECT IDENTIFIER
 */

/**
  Decode OID data and store the array of integers in words
  @param in      The OID DER encoded data
  @param inlen   The length of the OID data
  @param words   [out] The destination of the OID words
  @param outlen  [in/out] The number of OID words
  @return CRYPT_OK if successful
*/
int der_decode_object_identifier(const unsigned char *in,    unsigned long  inlen,
                                       unsigned long *words, unsigned long *outlen)
{
   unsigned long x, y, t, len;

   LTC_ARGCHK(in     != NULL);
   LTC_ARGCHK(words  != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* header is at least 3 bytes */
   if (inlen < 3) {
      return CRYPT_INVALID_PACKET;
   }

   /* must be room for at least two words */
   if (*outlen < 2) {
      return CRYPT_BUFFER_OVERFLOW;
   }

   /* decode the packet header */
   x = 0;
   if ((in[x++] & 0x1F) != 0x06) {
      return CRYPT_INVALID_PACKET;
   }
   
   /* get the length */
   if (in[x] < 128) {
      len = in[x++]; 
   } else {
       if (in[x] < 0x81 || in[x] > 0x82) {
          return CRYPT_INVALID_PACKET;
       }
       y   = in[x++] & 0x7F;
       len = 0;
       while (y--) {
          len = (len << 8) | (unsigned long)in[x++];
       }
   }

   if (len < 1 || (len + x) > inlen) {
      return CRYPT_INVALID_PACKET;
   }

   /* decode words */
   y = 0;
   t = 0;
   while (len--) {
       t = (t << 7) | (in[x] & 0x7F);
       if (!(in[x++] & 0x80)) {
           /* store t */
           if (y >= *outlen) {
              return CRYPT_BUFFER_OVERFLOW;
           }
      if (y == 0) {
         words[0] = t / 40;
         words[1] = t % 40;
         y = 2;
      } else {
              words[y++] = t;
      }
           t          = 0;
       }
   }
       
   *outlen = y;
   return CRYPT_OK;
}

/**
  Encode an OID
  @param words   The words to encode  (upto 32-bits each)
  @param nwords  The number of words in the OID
  @param out     [out] Destination of OID data
  @param outlen  [in/out] The max and resulting size of the OID
  @return CRYPT_OK if successful
*/
int der_encode_object_identifier(unsigned long *words, unsigned long  nwords,
                                 unsigned char *out,   unsigned long *outlen)
{
   unsigned long i, x, y, z, t, mask, wordbuf;
   int           err;

   LTC_ARGCHK(words  != NULL);
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* check length */
   if ((err = der_length_object_identifier(words, nwords, &x)) != CRYPT_OK) {
      return err;
   }
   if (x > *outlen) {
      *outlen = x;
      return CRYPT_BUFFER_OVERFLOW;
   }

   /* compute length to store OID data */
   z = 0;
   wordbuf = words[0] * 40 + words[1];
   for (y = 1; y < nwords; y++) {
       t = der_object_identifier_bits(wordbuf);
       z += t/7 + ((t%7) ? 1 : 0) + (wordbuf == 0 ? 1 : 0);
       if (y < nwords - 1) {
          wordbuf = words[y + 1];
       }
   }

   /* store header + length */
   x = 0; 
   out[x++] = 0x06;
   if (z < 128) {
      out[x++] = (unsigned char)z;
   } else if (z < 256) {
      out[x++] = 0x81;
      out[x++] = (unsigned char)z;
   } else if (z < 65536UL) {
      out[x++] = 0x82;
      out[x++] = (unsigned char)((z>>8)&255);
      out[x++] = (unsigned char)(z&255);
   } else {
      return CRYPT_INVALID_ARG;
   }

   /* store first byte */
    wordbuf = words[0] * 40 + words[1];   
    for (i = 1; i < nwords; i++) {
        /* store 7 bit words in little endian */
        t    = wordbuf & 0xFFFFFFFF;
        if (t) {
           y    = x;
           mask = 0;
           while (t) {
               out[x++] = (unsigned char)((t & 0x7F) | mask);
               t    >>= 7;
               mask  |= 0x80;  /* upper bit is set on all but the last byte */
           }
           /* now swap bytes y...x-1 */
           z = x - 1;
           while (y < z) {
               t = out[y]; out[y] = out[z]; out[z] = (unsigned char)t;
               ++y; 
               --z;
           }
       } else {
          /* zero word */
          out[x++] = 0x00;
       }
       
       if (i < nwords - 1) {
          wordbuf = words[i + 1];
       }
   }

   *outlen = x;
   return CRYPT_OK;
}

unsigned long der_object_identifier_bits(unsigned long x)
{
   unsigned long c;
   x &= 0xFFFFFFFF;
   c  = 0;
   while (x) {
     ++c;
     x >>= 1;
   }
   return c;
}


/**
  Gets length of DER encoding of Object Identifier
  @param nwords   The number of OID words 
  @param words    The actual OID words to get the size of
  @param outlen   [out] The length of the DER encoding for the given string
  @return CRYPT_OK if successful
*/
int der_length_object_identifier(unsigned long *words, unsigned long nwords, unsigned long *outlen)
{
   unsigned long y, z, t, wordbuf;   

   LTC_ARGCHK(words  != NULL);
   LTC_ARGCHK(outlen != NULL);


   /* must be >= 2 words */
   if (nwords < 2) {
      return CRYPT_INVALID_ARG;
   }

   /* word1 = 0,1,2,3 and word2 0..39 */
   if (words[0] > 3 || (words[0] < 2 && words[1] > 39)) {
      return CRYPT_INVALID_ARG;
   }

   /* leading word is the first two */
   z = 0;
   wordbuf = words[0] * 40 + words[1];
   for (y = 1; y < nwords; y++) {
       t = der_object_identifier_bits(wordbuf);
       z += t/7 + ((t%7) ? 1 : 0) + (wordbuf == 0 ? 1 : 0);
       if (y < nwords - 1) {
          /* grab next word */
          wordbuf = words[y+1];
       }
   }

   /* now depending on the length our length encoding changes */
   if (z < 128) {
      z += 2;
   } else if (z < 256) {
      z += 3;
   } else if (z < 65536UL) {
      z += 4;
   } else {
      return CRYPT_INVALID_ARG;
   }

   *outlen = z;
   return CRYPT_OK;
}

/*
 * OCTECT
 */

/**
  Store a OCTET STRING
  @param in      The DER encoded OCTET STRING
  @param inlen   The size of the DER OCTET STRING
  @param out     [out] The array of octets stored (one per char)
  @param outlen  [in/out] The number of octets stored
  @return CRYPT_OK if successful
*/
int der_decode_octet_string(const unsigned char *in, unsigned long inlen,
                                  unsigned char *out, unsigned long *outlen)
{
   unsigned long x, y, len;

   LTC_ARGCHK(in     != NULL);
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* must have header at least */
   if (inlen < 2) {
      return CRYPT_INVALID_PACKET;
   }

   /* check for 0x04 */
   if ((in[0] & 0x1F) != 0x04) {
      return CRYPT_INVALID_PACKET;
   }
   x = 1;

   /* decode the length */
   if (in[x] & 0x80) {
      /* valid # of bytes in length are 1,2,3 */
      y = in[x] & 0x7F;
      if ((y == 0) || (y > 3) || ((x + y) > inlen)) {
         return CRYPT_INVALID_PACKET;
      }

      /* read the length in */
      len = 0;
      ++x;
      while (y--) {
         len = (len << 8) | in[x++];
      }
   } else {
      len = in[x++] & 0x7F;
   }

   /* is it too long? */
   if (len > *outlen) {
      *outlen = len;
      return CRYPT_BUFFER_OVERFLOW;
   }

   if (len + x > inlen) {
      return CRYPT_INVALID_PACKET;
   }

   /* read the data */
   for (y = 0; y < len; y++) {
       out[y] = in[x++];
   }

   *outlen = y;

   return CRYPT_OK;
}

/**
  Store an OCTET STRING
  @param in       The array of OCTETS to store (one per char)
  @param inlen    The number of OCTETS to store
  @param out      [out] The destination for the DER encoded OCTET STRING
  @param outlen   [in/out] The max size and resulting size of the DER OCTET STRING
  @return CRYPT_OK if successful
*/
int der_encode_octet_string(const unsigned char *in, unsigned long inlen,
                                  unsigned char *out, unsigned long *outlen)
{
   unsigned long x, y, len;
   int           err;

   LTC_ARGCHK(in     != NULL);
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* get the size */
   if ((err = der_length_octet_string(inlen, &len)) != CRYPT_OK) {
      return err; 
   }

   /* too big? */
   if (len > *outlen) {
      *outlen = len;
      return CRYPT_BUFFER_OVERFLOW;
   }

   /* encode the header+len */
   x = 0;
   out[x++] = 0x04;
   if (inlen < 128) {
      out[x++] = (unsigned char)inlen;
   } else if (inlen < 256) {
      out[x++] = 0x81;
      out[x++] = (unsigned char)inlen;
   } else if (inlen < 65536UL) {
      out[x++] = 0x82;
      out[x++] = (unsigned char)((inlen>>8)&255);
      out[x++] = (unsigned char)(inlen&255);
   } else if (inlen < 16777216UL) {
      out[x++] = 0x83;
      out[x++] = (unsigned char)((inlen>>16)&255);
      out[x++] = (unsigned char)((inlen>>8)&255);
      out[x++] = (unsigned char)(inlen&255);
   } else {
      return CRYPT_INVALID_ARG;
   }

   /* store octets */
   for (y = 0; y < inlen; y++) {
       out[x++] = in[y];
   }

   /* retun length */
   *outlen = x;

   return CRYPT_OK;
}

/**
  Gets length of DER encoding of OCTET STRING 
  @param noctets  The number of octets in the string to encode
  @param outlen   [out] The length of the DER encoding for the given string
  @return CRYPT_OK if successful
*/
int der_length_octet_string(unsigned long noctets, unsigned long *outlen)
{
   LTC_ARGCHK(outlen != NULL);

   if (noctets < 128) {
      /* 04 LL DD DD DD ... */
      *outlen = 2 + noctets;
   } else if (noctets < 256) {
      /* 04 81 LL DD DD DD ... */
      *outlen = 3 + noctets;
   } else if (noctets < 65536UL) {
      /* 04 82 LL LL DD DD DD ... */
      *outlen = 4 + noctets;
   } else if (noctets < 16777216UL) {
      /* 04 83 LL LL LL DD DD DD ... */
      *outlen = 5 + noctets;
   } else {
      return CRYPT_INVALID_ARG;
   }

   return CRYPT_OK;
}

/*
 * PRINTABLE STRINg
 */

/**
  Store a printable STRING
  @param in      The DER encoded printable STRING
  @param inlen   The size of the DER printable STRING
  @param out     [out] The array of octets stored (one per char)
  @param outlen  [in/out] The number of octets stored
  @return CRYPT_OK if successful
*/
int der_decode_printable_string(const unsigned char *in, unsigned long inlen,
                                unsigned char *out, unsigned long *outlen)
{
   unsigned long x, y, len;
   int           t;

   LTC_ARGCHK(in     != NULL);
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* must have header at least */
   if (inlen < 2) {
      return CRYPT_INVALID_PACKET;
   }

   /* check for 0x13 */
   if ((in[0] & 0x1F) != 0x13) {
      return CRYPT_INVALID_PACKET;
   }
   x = 1;

   /* decode the length */
   if (in[x] & 0x80) {
      /* valid # of bytes in length are 1,2,3 */
      y = in[x] & 0x7F;
      if ((y == 0) || (y > 3) || ((x + y) > inlen)) {
         return CRYPT_INVALID_PACKET;
      }

      /* read the length in */
      len = 0;
      ++x;
      while (y--) {
         len = (len << 8) | in[x++];
      }
   } else {
      len = in[x++] & 0x7F;
   }

   /* is it too long? */
   if (len > *outlen) {
      *outlen = len;
      return CRYPT_BUFFER_OVERFLOW;
   }

   if (len + x > inlen) {
      return CRYPT_INVALID_PACKET;
   }

   /* read the data */
   for (y = 0; y < len; y++) {
       t = der_printable_value_decode(in[x++]);
       if (t == -1) {
           return CRYPT_INVALID_ARG;
       }
       out[y] = t;
   }

   *outlen = y;

   return CRYPT_OK;
}

/**
  Store an printable STRING
  @param in       The array of printable to store (one per char)
  @param inlen    The number of printable to store
  @param out      [out] The destination for the DER encoded printable STRING
  @param outlen   [in/out] The max size and resulting size of the DER printable STRING
  @return CRYPT_OK if successful
*/
int der_encode_printable_string(const unsigned char *in, unsigned long inlen,
                                unsigned char *out, unsigned long *outlen)
{
   unsigned long x, y, len;
   int           err;

   LTC_ARGCHK(in     != NULL);
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* get the size */
   if ((err = der_length_printable_string(in, inlen, &len)) != CRYPT_OK) {
      return err; 
   }

   /* too big? */
   if (len > *outlen) {
      *outlen = len;
      return CRYPT_BUFFER_OVERFLOW;
   }

   /* encode the header+len */
   x = 0;
   out[x++] = 0x13;
   if (inlen < 128) {
      out[x++] = (unsigned char)inlen;
   } else if (inlen < 256) {
      out[x++] = 0x81;
      out[x++] = (unsigned char)inlen;
   } else if (inlen < 65536UL) {
      out[x++] = 0x82;
      out[x++] = (unsigned char)((inlen>>8)&255);
      out[x++] = (unsigned char)(inlen&255);
   } else if (inlen < 16777216UL) {
      out[x++] = 0x83;
      out[x++] = (unsigned char)((inlen>>16)&255);
      out[x++] = (unsigned char)((inlen>>8)&255);
      out[x++] = (unsigned char)(inlen&255);
   } else {
      return CRYPT_INVALID_ARG;
   }

   /* store octets */
   for (y = 0; y < inlen; y++) {
       out[x++] = der_printable_char_encode(in[y]);
   }

   /* retun length */
   *outlen = x;

   return CRYPT_OK;
}

static const struct {
   int code, value;
} printable_table[] = {
{ ' ', 32 }, 
{ '\'', 39 }, 
{ '(', 40 }, 
{ ')', 41 }, 
{ '+', 43 }, 
{ ',', 44 }, 
{ '-', 45 }, 
{ '.', 46 }, 
{ '/', 47 }, 
{ '0', 48 }, 
{ '1', 49 }, 
{ '2', 50 }, 
{ '3', 51 }, 
{ '4', 52 }, 
{ '5', 53 }, 
{ '6', 54 }, 
{ '7', 55 }, 
{ '8', 56 }, 
{ '9', 57 }, 
{ ':', 58 }, 
{ '=', 61 }, 
{ '?', 63 }, 
{ 'A', 65 }, 
{ 'B', 66 }, 
{ 'C', 67 }, 
{ 'D', 68 }, 
{ 'E', 69 }, 
{ 'F', 70 }, 
{ 'G', 71 }, 
{ 'H', 72 }, 
{ 'I', 73 }, 
{ 'J', 74 }, 
{ 'K', 75 }, 
{ 'L', 76 }, 
{ 'M', 77 }, 
{ 'N', 78 }, 
{ 'O', 79 }, 
{ 'P', 80 }, 
{ 'Q', 81 }, 
{ 'R', 82 }, 
{ 'S', 83 }, 
{ 'T', 84 }, 
{ 'U', 85 }, 
{ 'V', 86 }, 
{ 'W', 87 }, 
{ 'X', 88 }, 
{ 'Y', 89 }, 
{ 'Z', 90 }, 
{ 'a', 97 }, 
{ 'b', 98 }, 
{ 'c', 99 }, 
{ 'd', 100 }, 
{ 'e', 101 }, 
{ 'f', 102 }, 
{ 'g', 103 }, 
{ 'h', 104 }, 
{ 'i', 105 }, 
{ 'j', 106 }, 
{ 'k', 107 }, 
{ 'l', 108 }, 
{ 'm', 109 }, 
{ 'n', 110 }, 
{ 'o', 111 }, 
{ 'p', 112 }, 
{ 'q', 113 }, 
{ 'r', 114 }, 
{ 's', 115 }, 
{ 't', 116 }, 
{ 'u', 117 }, 
{ 'v', 118 }, 
{ 'w', 119 }, 
{ 'x', 120 }, 
{ 'y', 121 }, 
{ 'z', 122 }, 
};

int der_printable_char_encode(int c)
{
   int x;
   for (x = 0; x < (int)(sizeof(printable_table)/sizeof(printable_table[0])); x++) {
       if (printable_table[x].code == c) {
          return printable_table[x].value;
       }
   }
   return -1;
}

int der_printable_value_decode(int v)
{
   int x;
   for (x = 0; x < (int)(sizeof(printable_table)/sizeof(printable_table[0])); x++) {
       if (printable_table[x].value == v) {
          return printable_table[x].code;
       }
   }
   return -1;
}
   
/**
  Gets length of DER encoding of Printable STRING 
  @param octets   The values you want to encode 
  @param noctets  The number of octets in the string to encode
  @param outlen   [out] The length of the DER encoding for the given string
  @return CRYPT_OK if successful
*/
int der_length_printable_string(const unsigned char *octets, unsigned long noctets, unsigned long *outlen)
{
   unsigned long x;

   LTC_ARGCHK(outlen != NULL);
   LTC_ARGCHK(octets != NULL);

   /* scan string for validity */
   for (x = 0; x < noctets; x++) {
       if (der_printable_char_encode(octets[x]) == -1) {
          return CRYPT_INVALID_ARG;
       }
   }

   if (noctets < 128) {
      /* 16 LL DD DD DD ... */
      *outlen = 2 + noctets;
   } else if (noctets < 256) {
      /* 16 81 LL DD DD DD ... */
      *outlen = 3 + noctets;
   } else if (noctets < 65536UL) {
      /* 16 82 LL LL DD DD DD ... */
      *outlen = 4 + noctets;
   } else if (noctets < 16777216UL) {
      /* 16 83 LL LL LL DD DD DD ... */
      *outlen = 5 + noctets;
   } else {
      return CRYPT_INVALID_ARG;
   }

   return CRYPT_OK;
}

/*
 * SET
 */

/* LTC define to ASN.1 TAG */
static int ltc_to_asn1(int v)
{
   switch (v) {
      case LTC_ASN1_BOOLEAN:                 return 0x01;
      case LTC_ASN1_INTEGER:
      case LTC_ASN1_SHORT_INTEGER:           return 0x02;
      case LTC_ASN1_BIT_STRING:              return 0x03;
      case LTC_ASN1_OCTET_STRING:            return 0x04;
      case LTC_ASN1_NULL:                    return 0x05;
      case LTC_ASN1_OBJECT_IDENTIFIER:       return 0x06;
      case LTC_ASN1_UTF8_STRING:             return 0x0C;
      case LTC_ASN1_PRINTABLE_STRING:        return 0x13;
      case LTC_ASN1_IA5_STRING:              return 0x16;
      case LTC_ASN1_UTCTIME:                 return 0x17;
      case LTC_ASN1_SEQUENCE:                return 0x30;
      case LTC_ASN1_SET:
      case LTC_ASN1_SETOF:                   return 0x31;
      default: return -1;
   }
}         
      

static int qsort_helper(const void *a, const void *b)
{
   ltc_asn1_list *A = (ltc_asn1_list *)a, *B = (ltc_asn1_list *)b;
   int            r;
   
   r = ltc_to_asn1(A->type) - ltc_to_asn1(B->type);
   
   /* for QSORT the order is UNDEFINED if they are "equal" which means it is NOT DETERMINISTIC.  So we force it to be :-) */
   if (r == 0) {
      /* their order in the original list now determines the position */
      return A->used - B->used;
   } else {
      return r;
   }
}   

/*
   Encode a SET type
   @param list      The list of items to encode
   @param inlen     The number of items in the list
   @param out       [out] The destination 
   @param outlen    [in/out] The size of the output
   @return CRYPT_OK on success
*/
int der_encode_set(ltc_asn1_list *list, unsigned long inlen,
                   unsigned char *out,  unsigned long *outlen)
{
   ltc_asn1_list  *copy;
   unsigned long   x;
   int             err;
   
   /* make copy of list */
   copy = XCALLOC(inlen, sizeof(*copy));
   if (copy == NULL) {
      return CRYPT_MEM;
   }      
   
   /* fill in used member with index so we can fully sort it */
   for (x = 0; x < inlen; x++) {
       copy[x]      = list[x];
       copy[x].used = x;
   }       
   
   /* sort it by the "type" field */
   XQSORT(copy, inlen, sizeof(*copy), &qsort_helper);   
   
   /* call der_encode_sequence_ex() */
   err = der_encode_sequence_ex(copy, inlen, out, outlen, LTC_ASN1_SET);   
   
   /* free list */
   XFREE(copy);
   
   return err;
}                   

struct edge {
   unsigned char *start;
   unsigned long  size;
};

static int setof_qsort_helper(const void *a, const void *b)
{
   struct edge   *A = (struct edge *)a, *B = (struct edge *)b;
   int            r;
   unsigned long  x;
   
   /* compare min length */
   r = XMEMCMP(A->start, B->start, MIN(A->size, B->size));
   
   if (r == 0 && A->size != B->size) {
      if (A->size > B->size) {
         for (x = B->size; x < A->size; x++) {
            if (A->start[x]) {
               return 1;
            }
         }
      } else {
         for (x = A->size; x < B->size; x++) {
            if (B->start[x]) {
               return -1;
            }
         }
      }         
   }
   
   return r;      
}

/**
   Encode a SETOF stucture
   @param list      The list of items to encode
   @param inlen     The number of items in the list
   @param out       [out] The destination 
   @param outlen    [in/out] The size of the output
   @return CRYPT_OK on success
*/   
int der_encode_setof(ltc_asn1_list *list, unsigned long inlen,
                     unsigned char *out,  unsigned long *outlen)
{
   unsigned long  x, y, z, hdrlen;
   int            err;
   struct edge   *edges;
   unsigned char *ptr, *buf;
   
   /* check that they're all the same type */
   for (x = 1; x < inlen; x++) {
      if (list[x].type != list[x-1].type) {
         return CRYPT_INVALID_ARG;
      }
   }

   /* alloc buffer to store copy of output */
   buf = XCALLOC(1, *outlen);
   if (buf == NULL) {
      return CRYPT_MEM;
   }      
                  
   /* encode list */
   if ((err = der_encode_sequence_ex(list, inlen, buf, outlen, LTC_ASN1_SETOF)) != CRYPT_OK) {
       XFREE(buf);
       return err;
   }
   
   /* allocate edges */
   edges = XCALLOC(inlen, sizeof(*edges));
   if (edges == NULL) {
      XFREE(buf);
      return CRYPT_MEM;
   }      
   
   /* skip header */
      ptr = buf + 1;

      /* now skip length data */
      x = *ptr++;
      if (x >= 0x80) {
         ptr += (x & 0x7F);
      }
      
      /* get the size of the static header */
      hdrlen = ((unsigned long)ptr) - ((unsigned long)buf);
      
      
   /* scan for edges */
   x = 0;
   while (ptr < (buf + *outlen)) {
      /* store start */
      edges[x].start = ptr;
      
      /* skip type */
      z = 1;
      
      /* parse length */
      y = ptr[z++];
      if (y < 128) {
         edges[x].size = y;
      } else {
         y &= 0x7F;
         edges[x].size = 0;
         while (y--) {
            edges[x].size = (edges[x].size << 8) | ((unsigned long)ptr[z++]);
         }
      }
      
      /* skip content */
      edges[x].size += z;
      ptr           += edges[x].size;
      ++x;
   }      
      
   /* sort based on contents (using edges) */
   XQSORT(edges, inlen, sizeof(*edges), &setof_qsort_helper);
   
   /* copy static header */
   XMEMCPY(out, buf, hdrlen);
   
   /* copy+sort using edges+indecies to output from buffer */
   for (y = hdrlen, x = 0; x < inlen; x++) {
      XMEMCPY(out+y, edges[x].start, edges[x].size);
      y += edges[x].size;
   }      
   
#ifdef LTC_CLEAN_STACK
   zeromem(buf, *outlen);
#endif      
   
   /* free buffers */
   XFREE(edges);
   XFREE(buf);
   
   return CRYPT_OK;
}

/*
 * SHORT INTEGER
 */

/**
  Read a short integer
  @param in       The DER encoded data
  @param inlen    Size of data
  @param num      [out] The integer to decode
  @return CRYPT_OK if successful
*/
int der_decode_short_integer(const unsigned char *in, unsigned long inlen, unsigned long *num)
{
   unsigned long len, x, y;

   LTC_ARGCHK(num    != NULL);
   LTC_ARGCHK(in     != NULL);

   /* check length */
   if (inlen < 2) {
      return CRYPT_INVALID_PACKET;
   }

   /* check header */
   x = 0;
   if ((in[x++] & 0x1F) != 0x02) {
      return CRYPT_INVALID_PACKET;
   }

   /* get the packet len */
   len = in[x++];

   if (x + len > inlen) {
      return CRYPT_INVALID_PACKET;
   }

   /* read number */
   y = 0;
   while (len--) {
      y = (y<<8) | (unsigned long)in[x++];
   }
   *num = y;

   return CRYPT_OK;

}

/**
  Store a short integer in the range (0,2^32-1)
  @param num      The integer to encode
  @param out      [out] The destination for the DER encoded integers
  @param outlen   [in/out] The max size and resulting size of the DER encoded integers
  @return CRYPT_OK if successful
*/
int der_encode_short_integer(unsigned long num, unsigned char *out, unsigned long *outlen)
{  
   unsigned long len, x, y, z;
   int           err;
   
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* force to 32 bits */
   num &= 0xFFFFFFFFUL;

   /* find out how big this will be */
   if ((err = der_length_short_integer(num, &len)) != CRYPT_OK) {
      return err;
   }

   if (*outlen < len) {
      *outlen = len;
      return CRYPT_BUFFER_OVERFLOW;
   }

   /* get len of output */
   z = 0;
   y = num;
   while (y) {
     ++z;
     y >>= 8;
   }

   /* handle zero */
   if (z == 0) {
      z = 1;
   }

   /* see if msb is set */
   z += (num&(1UL<<((z<<3) - 1))) ? 1 : 0;

   /* adjust the number so the msB is non-zero */
   for (x = 0; (z <= 4) && (x < (4 - z)); x++) {
      num <<= 8;
   }

   /* store header */
   x = 0;
   out[x++] = 0x02;
   out[x++] = (unsigned char)z;

   /* if 31st bit is set output a leading zero and decrement count */
   if (z == 5) {
      out[x++] = 0;
      --z;
   }

   /* store values */
   for (y = 0; y < z; y++) {
      out[x++] = (unsigned char)((num >> 24) & 0xFF);
      num    <<= 8;
   }

   /* we good */
   *outlen = x;
 
   return CRYPT_OK;
}

/**
  Gets length of DER encoding of num 
  @param num    The integer to get the size of 
  @param outlen [out] The length of the DER encoding for the given integer
  @return CRYPT_OK if successful
*/
int der_length_short_integer(unsigned long num, unsigned long *outlen)
{
   unsigned long z, y, len;

   LTC_ARGCHK(outlen  != NULL);

   /* force to 32 bits */
   num &= 0xFFFFFFFFUL;

   /* get the number of bytes */
   z = 0;
   y = num;
   while (y) {
     ++z;
     y >>= 8;
   }
   
   /* handle zero */
   if (z == 0) {
      z = 1;
   }

   /* we need a 0x02 to indicate it's INTEGER */
   len = 1;

   /* length byte */
   ++len;

   /* bytes in value */
   len += z;

   /* see if msb is set */
   len += (num&(1UL<<((z<<3) - 1))) ? 1 : 0;

   /* return length */
   *outlen = len; 
   
   return CRYPT_OK;
}

/*
 * UTCTIME
 */
 
static int char_to_int(unsigned char x)
{
   switch (x)  {
      case '0': return 0;
      case '1': return 1;
      case '2': return 2;
      case '3': return 3;
      case '4': return 4;
      case '5': return 5;
      case '6': return 6;
      case '7': return 7;
      case '8': return 8;
      case '9': return 9;
   }
   return 100;
}

#define DECODE_V(y, max) \
   y  = char_to_int(buf[x])*10 + char_to_int(buf[x+1]); \
   if (y >= max) return CRYPT_INVALID_PACKET;           \
   x += 2;

/**
  Decodes a UTC time structure in DER format (reads all 6 valid encoding formats)
  @param in     Input buffer
  @param inlen  Length of input buffer in octets
  @param out    [out] Destination of UTC time structure
  @return CRYPT_OK   if successful
*/
int der_decode_utctime(const unsigned char *in, unsigned long *inlen,
                             ltc_utctime   *out)
{
   unsigned char buf[32];
   unsigned long x;
   int           y;

   LTC_ARGCHK(in    != NULL);
   LTC_ARGCHK(inlen != NULL);
   LTC_ARGCHK(out   != NULL);

   /* check header */
   if (*inlen < 2UL || (in[1] >= sizeof(buf)) || ((in[1] + 2UL) > *inlen)) {
      return CRYPT_INVALID_PACKET;
   }

   /* decode the string */
   for (x = 0; x < in[1]; x++) {
       y = der_ia5_value_decode(in[x+2]);
       if (y == -1) {
          return CRYPT_INVALID_PACKET;
       }
       buf[x] = y;
   }
   *inlen = 2 + x;


   /* possible encodings are 
YYMMDDhhmmZ
YYMMDDhhmm+hh'mm'
YYMMDDhhmm-hh'mm'
YYMMDDhhmmssZ
YYMMDDhhmmss+hh'mm'
YYMMDDhhmmss-hh'mm'

    So let's do a trivial decode upto [including] mm 
   */

    x = 0;
    DECODE_V(out->YY, 100);
    DECODE_V(out->MM, 13);
    DECODE_V(out->DD, 32);
    DECODE_V(out->hh, 24);
    DECODE_V(out->mm, 60);

    /* clear timezone and seconds info */
    out->off_dir = out->off_hh = out->off_mm = out->ss = 0;

    /* now is it Z, +, - or 0-9 */
    if (buf[x] == 'Z') {
       return CRYPT_OK;
    } else if (buf[x] == '+' || buf[x] == '-') {
       out->off_dir = (buf[x++] == '+') ? 0 : 1;
       DECODE_V(out->off_hh, 24);
       DECODE_V(out->off_mm, 60);
       return CRYPT_OK;
    }

    /* decode seconds */
    DECODE_V(out->ss, 60);

    /* now is it Z, +, - */
    if (buf[x] == 'Z') {
       return CRYPT_OK;
    } else if (buf[x] == '+' || buf[x] == '-') {
       out->off_dir = (buf[x++] == '+') ? 0 : 1;
       DECODE_V(out->off_hh, 24);
       DECODE_V(out->off_mm, 60);
       return CRYPT_OK;
    } else {
       return CRYPT_INVALID_PACKET;
    }
}


static const char *baseten = "0123456789";

#define STORE_V(y) \
    out[x++] = der_ia5_char_encode(baseten[(y/10) % 10]); \
    out[x++] = der_ia5_char_encode(baseten[y % 10]);

/**
  Encodes a UTC time structure in DER format
  @param utctime      The UTC time structure to encode
  @param out          The destination of the DER encoding of the UTC time structure
  @param outlen       [in/out] The length of the DER encoding
  @return CRYPT_OK if successful
*/
int der_encode_utctime(ltc_utctime *utctime, 
                       unsigned char *out,   unsigned long *outlen)
{
    unsigned long x, tmplen;
    int           err;
 
    LTC_ARGCHK(utctime != NULL);
    LTC_ARGCHK(out     != NULL);
    LTC_ARGCHK(outlen  != NULL);

    if ((err = der_length_utctime(utctime, &tmplen)) != CRYPT_OK) {
       return err;
    }
    if (tmplen > *outlen) {
        *outlen = tmplen;
        return CRYPT_BUFFER_OVERFLOW;
    }
    
    /* store header */
    out[0] = 0x17;

    /* store values */
    x = 2;
    STORE_V(utctime->YY);
    STORE_V(utctime->MM);
    STORE_V(utctime->DD);
    STORE_V(utctime->hh);
    STORE_V(utctime->mm);
    STORE_V(utctime->ss);

    if (utctime->off_mm || utctime->off_hh) {
       out[x++] = der_ia5_char_encode(utctime->off_dir ? '-' : '+');
       STORE_V(utctime->off_hh);
       STORE_V(utctime->off_mm);
    } else {
       out[x++] = der_ia5_char_encode('Z');
    }

    /* store length */
    out[1] = (unsigned char)(x - 2);
   
    /* all good let's return */
    *outlen = x;
    return CRYPT_OK;
}

/**
  Gets length of DER encoding of UTCTIME
  @param utctime      The UTC time structure to get the size of
  @param outlen [out] The length of the DER encoding
  @return CRYPT_OK if successful
*/
int der_length_utctime(ltc_utctime *utctime, unsigned long *outlen)
{
   LTC_ARGCHK(outlen  != NULL);
   LTC_ARGCHK(utctime != NULL);

   if (utctime->off_hh == 0 && utctime->off_mm == 0) {
      /* we encode as YYMMDDhhmmssZ */
      *outlen = 2 + 13;
   } else {
      /* we encode as YYMMDDhhmmss{+|-}hh'mm' */
      *outlen = 2 + 17;
   }

   return CRYPT_OK;
}

/*
 * UTF8
 */

/**
  Store a UTF8 STRING
  @param in      The DER encoded UTF8 STRING
  @param inlen   The size of the DER UTF8 STRING
  @param out     [out] The array of utf8s stored (one per char)
  @param outlen  [in/out] The number of utf8s stored
  @return CRYPT_OK if successful
*/
int der_decode_utf8_string(const unsigned char *in,  unsigned long inlen,
                                       wchar_t *out, unsigned long *outlen)
{
   wchar_t       tmp;
   unsigned long x, y, z, len;

   LTC_ARGCHK(in     != NULL);
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* must have header at least */
   if (inlen < 2) {
      return CRYPT_INVALID_PACKET;
   }

   /* check for 0x0C */
   if ((in[0] & 0x1F) != 0x0C) {
      return CRYPT_INVALID_PACKET;
   }
   x = 1;

   /* decode the length */
   if (in[x] & 0x80) {
      /* valid # of bytes in length are 1,2,3 */
      y = in[x] & 0x7F;
      if ((y == 0) || (y > 3) || ((x + y) > inlen)) {
         return CRYPT_INVALID_PACKET;
      }

      /* read the length in */
      len = 0;
      ++x;
      while (y--) {
         len = (len << 8) | in[x++];
      }
   } else {
      len = in[x++] & 0x7F;
   }

   if (len + x > inlen) {
      return CRYPT_INVALID_PACKET;
   }

   /* proceed to decode */
   for (y = 0; x < inlen; ) {
      /* get first byte */
      tmp = in[x++];
 
      /* count number of bytes */
      for (z = 0; (tmp & 0x80) && (z <= 4); z++, tmp = (tmp << 1) & 0xFF);
      
      if (z > 4 || (x + (z - 1) > inlen)) {
         return CRYPT_INVALID_PACKET;
      }

      /* decode, grab upper bits */
      tmp >>= z;

      /* grab remaining bytes */
      if (z > 1) { --z; }
      while (z-- != 0) {
         if ((in[x] & 0xC0) != 0x80) {
            return CRYPT_INVALID_PACKET;
         }
         tmp = (tmp << 6) | ((wchar_t)in[x++] & 0x3F);
      }

      if (y > *outlen) {
         *outlen = y;
         return CRYPT_BUFFER_OVERFLOW;
      }
      out[y++] = tmp;
   }
   *outlen = y;

   return CRYPT_OK;
}

/**
  Store an UTF8 STRING
  @param in       The array of UTF8 to store (one per wchar_t)
  @param inlen    The number of UTF8 to store
  @param out      [out] The destination for the DER encoded UTF8 STRING
  @param outlen   [in/out] The max size and resulting size of the DER UTF8 STRING
  @return CRYPT_OK if successful
*/
int der_encode_utf8_string(const wchar_t *in,  unsigned long inlen,
                           unsigned char *out, unsigned long *outlen)
{
   unsigned long x, y, len;

   LTC_ARGCHK(in     != NULL);
   LTC_ARGCHK(out    != NULL);
   LTC_ARGCHK(outlen != NULL);

   /* get the size */
   for (x = len = 0; x < inlen; x++) {
       if (in[x] < 0 || in[x] > 0x1FFFF) { 
          return CRYPT_INVALID_ARG;
       }
       len += der_utf8_charsize(in[x]);
   }

   if (len < 128) {
      y = 2 + len;
   } else if (len < 256) {
      y = 3 + len;
   } else if (len < 65536UL) {
      y = 4 + len;
   } else if (len < 16777216UL) {
      y = 5 + len;
   } else {
      return CRYPT_INVALID_ARG;
   }

   /* too big? */
   if (y > *outlen) {
      *outlen = len;
      return CRYPT_BUFFER_OVERFLOW;
   }

   /* encode the header+len */
   x = 0;
   out[x++] = 0x0C;
   if (len < 128) {
      out[x++] = (unsigned char)len;
   } else if (len < 256) {
      out[x++] = 0x81;
      out[x++] = (unsigned char)len;
   } else if (len < 65536UL) {
      out[x++] = 0x82;
      out[x++] = (unsigned char)((len>>8)&255);
      out[x++] = (unsigned char)(len&255);
   } else if (len < 16777216UL) {
      out[x++] = 0x83;
      out[x++] = (unsigned char)((len>>16)&255);
      out[x++] = (unsigned char)((len>>8)&255);
      out[x++] = (unsigned char)(len&255);
   } else {
      return CRYPT_INVALID_ARG;
   }

   /* store UTF8 */
   for (y = 0; y < inlen; y++) {
       switch (der_utf8_charsize(in[y])) {
          case 1: out[x++] = (unsigned char)in[y]; break;
          case 2: out[x++] = 0xC0 | ((in[y] >> 6) & 0x1F);  out[x++] = 0x80 | (in[y] & 0x3F); break;
          case 3: out[x++] = 0xE0 | ((in[y] >> 12) & 0x0F); out[x++] = 0x80 | ((in[y] >> 6) & 0x3F); out[x++] = 0x80 | (in[y] & 0x3F); break;
          case 4: out[x++] = 0xF0 | ((in[y] >> 18) & 0x07); out[x++] = 0x80 | ((in[y] >> 12) & 0x3F); out[x++] = 0x80 | ((in[y] >> 6) & 0x3F); out[x++] = 0x80 | (in[y] & 0x3F); break;
       }
   }

   /* retun length */
   *outlen = x;

   return CRYPT_OK;
}

/** Return the size in bytes of a UTF-8 character
  @param c   The UTF-8 character to measure
  @return    The size in bytes
*/
unsigned long der_utf8_charsize(const wchar_t c)
{
   if (c <= 0x7F) {
      return 1;
   } else if (c <= 0x7FF) {
      return 2;
   } else if (c <= 0xFFFF) {
      return 3;
   } else {
      return 4;
   }
}

/**
  Gets length of DER encoding of UTF8 STRING 
  @param in       The characters to measure the length of
  @param noctets  The number of octets in the string to encode
  @param outlen   [out] The length of the DER encoding for the given string
  @return CRYPT_OK if successful
*/
int der_length_utf8_string(const wchar_t *in, unsigned long noctets, unsigned long *outlen)
{
   unsigned long x, len;

   LTC_ARGCHK(in     != NULL);
   LTC_ARGCHK(outlen != NULL);

   len = 0;
   for (x = 0; x < noctets; x++) {
      if (in[x] < 0 || in[x] > 0x10FFFF) {
         return CRYPT_INVALID_ARG;
      }
      len += der_utf8_charsize(in[x]);
   }

   if (len < 128) {
      /* 0C LL DD DD DD ... */
      *outlen = 2 + len;
   } else if (len < 256) {
      /* 0C 81 LL DD DD DD ... */
      *outlen = 3 + len;
   } else if (len < 65536UL) {
      /* 0C 82 LL LL DD DD DD ... */
      *outlen = 4 + len;
   } else if (len < 16777216UL) {
      /* 0C 83 LL LL LL DD DD DD ... */
      *outlen = 5 + len;
   } else {
      return CRYPT_INVALID_ARG;
   }

   return CRYPT_OK;
}



/*
* SET
*/

