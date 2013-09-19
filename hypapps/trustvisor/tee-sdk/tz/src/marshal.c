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

/* 
 * Author - Jim Newsome (jnewsome@no-fuss.com)
 */

#include <tz.h>
#include <tzmarshal.h>

#define BUFFER_HEAD(psB) ((tzi_encoded_t*)((uintptr_t)(psB)->pBuf + (psB)->uiOffset))

/* #DEFINE BUF_PUSH(psB, d)                                                \ */
/*   do {                                                                  \ */
/*   if ((psB)->UiRetVal == TZ_SUCCESS) {                                  \ */
/*   if (((psB)->uiOffset + sizeof(d)) > (psB)->uiSize)                    \ */
/*   (psB)->uiRetVal = TZ_ERROR_ENCODE_MEMORY                              \ */
/*   else {                                                                \ */
/*   memcpy((psB)->pBuf, &(d), sizeof(d));                                 \ */
/*   (psB)->uiOffset += sizeof(d);                                         \ */
/*   }}                                                                    \ */
/*   } while(0) */

#define ALIGN_UP(uiX, uiAlign) ((((uiAlign) - (((uintptr_t)uiX) % (uiAlign))) % (uiAlign)) + ((uintptr_t)uiX));

/* use our own implementation of memcpy so that 
   it's available to PALs.
   XXX better solution?
*/
__attribute__ ((section (".stext")))
static void *memcpy(void *dest, const void *src, size_t n)
{
  size_t i;

  /* move a uint32_t at a time */
  for(i=0; i < (n / sizeof(uint32_t)); i++) {
    ((uint32_t*)dest)[i] = ((uint32_t*)src)[i];
  }

  /* now move a byte at a time */
  for(i=(n/sizeof(uint32_t)*sizeof(uint32_t)); i<n; i++) {
    ((uint8_t*)dest)[i] = ((uint8_t*)src)[i];
  }

  return dest;
}

__attribute__ ((section (".stext")))
void
TZIEncodeUint32(INOUT tzi_encode_buffer_t* psBuffer,
                uint32_t uiData)
{
  uint32_t sz = 
    sizeof(psBuffer->pBuf->uiType) 
    + sizeof(psBuffer->pBuf->sUint32);

  if (psBuffer->uiRetVal != TZ_SUCCESS) {
    return;
  } 

  if ((psBuffer->uiOffset + sz) > psBuffer->uiSize) {
    psBuffer->uiRetVal = TZ_ERROR_ENCODE_MEMORY;
    return;
  }

  BUFFER_HEAD(psBuffer)->uiType = TZI_ENCODED_UINT32;
  BUFFER_HEAD(psBuffer)->sUint32.uiValue = uiData;
  psBuffer->uiOffset += sz;
}

__attribute__ ((section (".stext")))
uint32_t
TZIDecodeUint32(INOUT tzi_encode_buffer_t* psBuffer)
{
  uint32_t rv;
  uint32_t sz = 
    sizeof(psBuffer->pBuf->uiType) 
    + sizeof(psBuffer->pBuf->sUint32);

  if (psBuffer->uiRetVal != TZ_SUCCESS) {
    return 0;
  }

  if ((psBuffer->uiOffset + sz) > psBuffer->uiSizeUsed) {
    psBuffer->uiRetVal = TZ_ERROR_DECODE_NO_DATA;
    return 0;
  }

  if (BUFFER_HEAD(psBuffer)->uiType != TZI_ENCODED_UINT32) {
    psBuffer->uiRetVal = TZ_ERROR_DECODE_TYPE;
    return 0;
  }

  rv = BUFFER_HEAD(psBuffer)->sUint32.uiValue;
  psBuffer->uiOffset += sz;

  return rv;
}


__attribute__ ((section (".stext")))
static void*
_TZIEncodeArraySpace(INOUT tzi_encode_buffer_t* psBuffer,
                     uint32_t uiLength)
{
  uint32_t sz = 
    sizeof(psBuffer->pBuf->uiType) 
    + sizeof(psBuffer->pBuf->sArray)
    + uiLength;
  uint32_t paddingBefore;
  uint32_t arrayUnalignedStartOffset;
  uint32_t arrayStartOffset;

  if (psBuffer->uiRetVal != TZ_SUCCESS) {
    return NULL;
  }

  /* standard guarantees that arrays are stored
   * at an 8-aligned address.
   * device should guarantee that base address
   * is 8-aligned.
   */
  arrayUnalignedStartOffset = psBuffer->uiOffset
    + sizeof(psBuffer->pBuf->uiType)
    + sizeof(psBuffer->pBuf->sArray);
  arrayStartOffset = ALIGN_UP(arrayUnalignedStartOffset, 8);
                              
  paddingBefore = arrayStartOffset - arrayUnalignedStartOffset;
  sz += paddingBefore;
  if ((psBuffer->uiOffset + sz) > psBuffer->uiSize) {
    psBuffer->uiRetVal = TZ_ERROR_ENCODE_MEMORY;
    return NULL;
  }

  BUFFER_HEAD(psBuffer)->uiType = TZI_ENCODED_ARRAY;
  BUFFER_HEAD(psBuffer)->sArray.uiSize = uiLength;

  /* we 4-align afterwards */
  psBuffer->uiOffset += ALIGN_UP(sz, 4);

  return &((uint8_t*)(psBuffer->pBuf))[arrayStartOffset];
}

uint32_t
TZIEncodeMemoryReference(INOUT tzi_encode_buffer_t* psBuffer,
                         IN void* pMem,
                         uint32_t Length)
{
  uint32_t sz =
    sizeof(psBuffer->pBuf->uiType)
    + sizeof(psBuffer->pBuf->sMem);
  uint32_t encodeOffset;

  if (psBuffer->uiRetVal != TZ_SUCCESS) {
    return 0;
  }

  if ((psBuffer->uiOffset + sz) > psBuffer->uiSize) {
    psBuffer->uiRetVal = TZ_ERROR_ENCODE_MEMORY;
    return 0;
  }

  encodeOffset = psBuffer->uiOffset + ((uintptr_t)(&BUFFER_HEAD(psBuffer)->sMem.pMem)
                                       - (uintptr_t)(BUFFER_HEAD(psBuffer)));

  BUFFER_HEAD(psBuffer)->uiType = TZI_ENCODED_MEM;
  BUFFER_HEAD(psBuffer)->sMem.uiSize = Length;
  BUFFER_HEAD(psBuffer)->sMem.pMem = pMem;
  psBuffer->uiOffset += sz;

  return encodeOffset;
}

__attribute__ ((section (".stext")))
void*
TZIDecodeMemoryReference(INOUT tzi_encode_buffer_t* psBuffer,
                         OUT uint32_t* puiLength)
{
  void* rv;
  uint32_t sz =
    sizeof(psBuffer->pBuf->uiType)
    + sizeof(psBuffer->pBuf->sMem);

  if (psBuffer->uiRetVal != TZ_SUCCESS) {
    return NULL;
  }

  if ((psBuffer->uiOffset + sz) > psBuffer->uiSizeUsed) {
    psBuffer->uiRetVal = TZ_ERROR_DECODE_NO_DATA;
    return NULL;
  }

  if (BUFFER_HEAD(psBuffer)->uiType != TZI_ENCODED_MEM) {
    psBuffer->uiRetVal = TZ_ERROR_DECODE_TYPE;
    return NULL;
  }

  rv = BUFFER_HEAD(psBuffer)->sMem.pMem;
  *puiLength = BUFFER_HEAD(psBuffer)->sMem.uiSize;
  psBuffer->uiOffset += sz;

  return rv;
}



__attribute__ ((section (".stext")))
void *
TZIDecodeArraySpace(INOUT tzi_encode_buffer_t* psBuffer,
                    OUT uint32_t* puiLength)
{
  uint32_t sz = 
    sizeof(psBuffer->pBuf->uiType) 
    + sizeof(psBuffer->pBuf->sArray);
  uint32_t paddingBefore;
  uint32_t arrayStartOffset;
  uint32_t arrayUnalignedStartOffset;

  if (psBuffer->uiRetVal != TZ_SUCCESS) {
    *puiLength = 0;
    return NULL;
  }

  /* first check that the header isn't off the end */
  if (psBuffer->uiOffset + sz > psBuffer->uiSizeUsed) {
    psBuffer->uiRetVal = TZ_ERROR_DECODE_NO_DATA;
    *puiLength = 0;
    return NULL;
  }

  /* type check */
  if (BUFFER_HEAD(psBuffer)->uiType != TZI_ENCODED_ARRAY) {
    psBuffer->uiRetVal = TZ_ERROR_DECODE_TYPE;
    *puiLength = 0;
    return NULL;
  }

  /* now make sure the whole array is here */
  *puiLength = BUFFER_HEAD(psBuffer)->sArray.uiSize;
  arrayUnalignedStartOffset = psBuffer->uiOffset
    + sizeof(psBuffer->pBuf->uiType)
    + sizeof(psBuffer->pBuf->sArray);
  arrayStartOffset = ALIGN_UP(arrayUnalignedStartOffset, 8);
  paddingBefore = arrayStartOffset - arrayUnalignedStartOffset;

  sz += paddingBefore;
  sz += *puiLength;
  if (psBuffer->uiOffset + sz > psBuffer->uiSizeUsed) {
    psBuffer->uiRetVal = TZ_ERROR_DECODE_NO_DATA;
    *puiLength = 0;
    return NULL;
  }
  
  psBuffer->uiOffset += ALIGN_UP(sz, 4);

  return &((uint8_t*)(psBuffer->pBuf))[arrayStartOffset];
}

__attribute__ ((section (".stext")))
void*
TZIEncodeArraySpace(INOUT tzi_encode_buffer_t* psBuffer,
                    uint32_t uiLength)
{
  void *m = _TZIEncodeArraySpace(psBuffer, uiLength);

  /* in case caller doesn't fill entire array,
   * prevent existing data from leaking.
   * XXX is this necessary? and if so, would it be
   * bigger to do one big memset on the encode buffer?
   */
  /* XXX revisit whether to do this
  if (m != NULL) {
    memset(m, 0, uiLength);
  }
  */
  return m;
}

__attribute__ ((section (".stext")))
void
TZIEncodeArray(INOUT tzi_encode_buffer_t* psBuffer,
               IN void const * pkArray,
               uint32_t uiLength)
{
  void *m = _TZIEncodeArraySpace(psBuffer, uiLength);
  if (m != NULL)
    memcpy(m, pkArray, uiLength);

}

__attribute__ ((section (".stext")))
tz_return_t
TZIDecodeGetError(INOUT tzi_encode_buffer_t* psBuffer)
{
  return psBuffer->uiRetVal;
}

__attribute__ ((section (".stext")))
void
TZIEncodeToDecode(INOUT tzi_encode_buffer_t* psBuffer)
{
  if (psBuffer->uiRetVal != TZ_SUCCESS)
    return;
  psBuffer->uiSizeUsed = psBuffer->uiOffset;
  psBuffer->uiOffset = 0;
}

__attribute__ ((section (".stext")))
void
TZIEncodeBufInit(INOUT tzi_encode_buffer_t* psBuffer, uint32_t uiLength)
{
  *psBuffer = (tzi_encode_buffer_t) {
    .uiRetVal = TZ_SUCCESS,
    .uiSize = uiLength - sizeof(tzi_encode_buffer_t),
    .uiOffset = 0,
    .uiSizeUsed = 0
  };
}

__attribute__ ((section (".stext")))
void
TZIEncodeBufReInit(INOUT tzi_encode_buffer_t* psBuffer)
{
  psBuffer->uiRetVal = TZ_SUCCESS;
  psBuffer->uiOffset = 0;
  psBuffer->uiSizeUsed = 0;
}

static int is_prefix(const char* prefix, const char* s)
{
  int i=0;

  while(1) {
    if (prefix[i] == '\0')
      return 1;

    if (prefix[i] != s[i])
      return 0;

    i++;
  }
}

static size_t strlen(const char *s)
{
  int i =0;
  while(s[i] != '\0')
    i++;
  return i;
}

tz_return_t
vTZIEncodeBufF(tzi_encode_buffer_t* psBuffer, const char* str, va_list argp)
{
  int i;

  while(1) {
    if(str[0] == '\0') {
      break;
    }
    if(str[0] != '%') {
      str++;
      continue;
    }
    str++; /* skip the '%' */

    if(is_prefix(TZI_EU32, str)) {
      str += strlen(TZI_EU32);
      TZIEncodeUint32(psBuffer, va_arg(argp, uint32_t));
    } else if (is_prefix(TZI_ESTR, str)) {
      char *s = va_arg(argp, char*);
      str += strlen(TZI_ESTR);
      TZIEncodeArray(psBuffer, s, strlen(s)+1);
    } else if (is_prefix(TZI_EARR, str)) {
      void *x = va_arg(argp, void*);
      uint32_t sz = va_arg(argp, uint32_t);
      str += strlen(TZI_EARR);

      TZIEncodeArray(psBuffer, x, sz);
    } else if (is_prefix(TZI_EARRSPC, str)) {
      void **x = va_arg(argp, void**);
      uint32_t sz = va_arg(argp, uint32_t);
      str += strlen(TZI_EARRSPC);

      *x = TZIEncodeArraySpace(psBuffer, sz);
    } else {
      return TZ_ERROR_ILLEGAL_ARGUMENT;
    }
  }
  return TZIDecodeGetError(psBuffer);
}

tz_return_t
TZIEncodeBufF(tzi_encode_buffer_t* psBuffer, const char* str, ...)
{
  tz_return_t rv;
  va_list argp;
  va_start(argp, str);
  rv = vTZIEncodeBufF(psBuffer, str, argp);
  va_end(argp);
  return rv;
}

static int is_prefix_ignore_splats(const char* prefix, const char* s)
{
  int i=0;

  while(1) {
    /* ignore splats. */
    while(*s == '*')
      s++;

    if (*prefix == '\0')
      return 1;

    if (*prefix != *s)
      return 0;

    prefix++;
    s++;
  }
}

tz_return_t
vTZIDecodeBufF(tzi_encode_buffer_t* psBuffer, const char* str, va_list argp)
{
  int i;

  while(1) {
    if(str[0] == '\0') {
      break;
    }
    if(str[0] != '%') {
      str++;
      continue;
    }
    str++; /* skip the '%' */

    /* we only decode array spaces and uint32's for now.  we *do*
       allow the '*' assignment-suppression character in the style of
       scanf. unfortunately that makes this code rather ugly and
       brittle, but hopefully makes client code a bit tidier. */

    if(is_prefix_ignore_splats(TZI_DU32, str)) {
      uint32_t i;
      i = TZIDecodeUint32(psBuffer);

      if (str[0] == '*') {
        str++;
      } else {
        uint32_t *pi = va_arg(argp, uint32_t*);
        *pi = i;
      }
      str += strlen(PRIu32);
    } else if (is_prefix_ignore_splats(TZI_DARRSPC, str)) {
      void *x=NULL;
      uint32_t sz;

      x = TZIDecodeArraySpace(psBuffer, &sz);

      if (str[0] == '*') {
        str++;
      } else {
        void **px = va_arg(argp, void**);
        *px = x;
      }
      str+=2; /* should now point after next '%' */

      if (str[0] == '*') {
        str++;
      } else {
        uint32_t *psz = va_arg(argp, uint32_t*);
        *psz = sz;
      }
      str+=strlen(PRIu32);
    } else if (is_prefix_ignore_splats(TZI_DARR, str)) {
      void *dst=NULL;
      void *src=NULL;
      uint32_t dst_sz, src_sz;
      uint32_t *pdst_sz = NULL;

      src = TZIDecodeArraySpace(psBuffer, &src_sz);

      if (str[0] == '*') {
        str++;
      } else {
        dst = va_arg(argp, void*);
      }
      str+=2; /* should now point after next '%' */

      if (str[0] == '*') {
        str++;
      } else {
        pdst_sz = va_arg(argp, uint32_t*);
        dst_sz = *pdst_sz;
        *pdst_sz = src_sz;
      }
      str+=strlen(PRIu32);

      if (dst) {
        if (!pdst_sz) {
          /* illegal to request data copy without specifying destination
             buffer size */
          return TZ_ERROR_ILLEGAL_ARGUMENT;
        }
        if (dst_sz < src_sz) {
          return TZ_ERROR_SHORT_BUFFER;
        }
        memcpy(dst, src, src_sz);
      }
    } else {
      return TZ_ERROR_ILLEGAL_ARGUMENT;
    }
  }
  return TZIDecodeGetError(psBuffer);
}

tz_return_t
TZIDecodeBufF(tzi_encode_buffer_t* psBuffer, const char* str, ...)
{
  tz_return_t rv;
  va_list argp;
  va_start(argp, str);
  rv = vTZIDecodeBufF(psBuffer, str, argp);
  va_end(argp);
  return rv;
}
