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

#include <tz.h>
#include <marshal.h>

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
__attribute__ ((section (".scode_util")))
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

__attribute__ ((section (".scode_util")))
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

__attribute__ ((section (".scode_util")))
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

__attribute__ ((section (".scode_util")))
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
  uint encodeOffset;

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


__attribute__ ((section (".scode_util")))
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

__attribute__ ((section (".scode_util")))
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

__attribute__ ((section (".scode_util")))
void
TZIEncodeArray(INOUT tzi_encode_buffer_t* psBuffer,
               IN void const * pkArray,
               uint32_t uiLength)
{
  void *m = _TZIEncodeArraySpace(psBuffer, uiLength);
  if (m != NULL)
    memcpy(m, pkArray, uiLength);

}

__attribute__ ((section (".scode_util")))
tz_return_t
TZIDecodeGetError(INOUT tzi_encode_buffer_t* psBuffer)
{
  return psBuffer->uiRetVal;
}

__attribute__ ((section (".scode_util")))
void
TZIEncodeToDecode(INOUT tzi_encode_buffer_t* psBuffer)
{
  if (psBuffer->uiRetVal != TZ_SUCCESS)
    return;
  psBuffer->uiSizeUsed = psBuffer->uiOffset;
  psBuffer->uiOffset = 0;
}

__attribute__ ((section (".scode_util")))
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

__attribute__ ((section (".scode_util")))
void
TZIEncodeBufReInit(INOUT tzi_encode_buffer_t* psBuffer)
{
  psBuffer->uiRetVal = TZ_SUCCESS;
  psBuffer->uiOffset = 0;
  psBuffer->uiSizeUsed = 0;
}
