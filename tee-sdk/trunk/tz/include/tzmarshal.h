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

#ifndef TZMARSHAL_H
#define TZMARSHAL_H

#include <stdarg.h>

#include "tz.h"

typedef enum tzi_encoded_type_t {
  TZI_ENCODED_UINT32,
  TZI_ENCODED_ARRAY,
  TZI_ENCODED_MEM,
} tzi_encoded_type_t;

typedef struct tzi_encoded_t {
  tzi_encoded_type_t uiType;
  union {
    struct {
      uint32_t uiValue;
    } sUint32;
    struct {
      uint32_t uiSize;
      uint8_t aData[]; /* there must be nothing after this union for
                          this to work! */
    } sArray;
    struct {
      uint32_t uiSize;
      void *pMem;
    } sMem;
  };
} tzi_encoded_t;

typedef struct tzi_encode_buffer_t {
  tz_return_t uiRetVal;
  uint32_t uiSize;
  uint32_t uiOffset;
  uint32_t uiSizeUsed; /* only valid when decoding */
  tzi_encoded_t pBuf[];/* CAUTION when adding members to this struct- 
                          pBuf must be 8-byte aligned. */
} tzi_encode_buffer_t;

void
TZIEncodeUint32(INOUT tzi_encode_buffer_t* psBuffer,
                uint32_t uiData);
uint32_t
TZIDecodeUint32(INOUT tzi_encode_buffer_t* psBuffer);

void
TZIEncodeArray(INOUT tzi_encode_buffer_t* psBuffer,
               IN void const * pkArray,
               uint32_t uiLength);
void*
TZIEncodeArraySpace(INOUT tzi_encode_buffer_t* psBuffer,
                    uint32_t uiLength);

uint32_t TZIEncodeMemoryReference(INOUT tzi_encode_buffer_t* psBuffer,
                                  IN void* pMem,
                                  uint32_t Length);

void*
TZIDecodeMemoryReference(INOUT tzi_encode_buffer_t* psBuffer,
                         OUT uint32_t* puiLength);

void *
TZIDecodeArraySpace(INOUT tzi_encode_buffer_t* psBuffer,
                    OUT uint32_t* puiLength);

void
TZIEncodeToDecode(INOUT tzi_encode_buffer_t* psBuffer);

void
TZIEncodeBufInit(INOUT tzi_encode_buffer_t* psBuffer, uint32_t uiLength);

void
TZIEncodeBufReInit(INOUT tzi_encode_buffer_t* psBuffer);

tz_return_t
TZIDecodeGetError(INOUT tzi_encode_buffer_t* psBuffer);

tz_return_t
vTZIEncodeBufF(tzi_encode_buffer_t* psBuffer, const char* str, va_list argp);

tz_return_t
TZIEncodeBufF(tzi_encode_buffer_t* psBuffer, const char* str, ...)
  __attribute__ ((format (printf, 2, 3)));

tz_return_t
vTZIDecodeBufF(tzi_encode_buffer_t* psBuffer, const char* str, va_list argp);

tz_return_t
TZIDecodeBufF(tzi_encode_buffer_t* psBuffer, const char* str, ...)
  __attribute__ ((format (scanf, 2, 3)));

#endif
