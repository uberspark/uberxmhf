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
#include <list.h>

#include <assert.h>
#include <string.h>

#define CBB_OF_DEVICE(d) ((d)->sImp.cbb)
#define CBB_OF_SESSION(s) (CBB_OF_DEVICE((s)->sImp.psDevice))
#define CBB_OF_OPERATION(o) (CBB_OF_SESSION((o)->sImp.psSession))
#define CBB_OF_SHAREDMEM(m) (CBB_OF_SESSION((m)->sImp.psSession))

#define TZI_DEVICE_REGISTRY_MAX 10
static size_t tzi_device_registry_count = 0;
static tzi_device_registry_entry_t tzi_device_registry[TZI_DEVICE_REGISTRY_MAX];

tz_return_t TZIDeviceRegister(const char *name, tzi_device_cb_block_t* cbb)
{
  if (tzi_device_registry_count >= TZI_DEVICE_REGISTRY_MAX) {
    return TZ_ERROR_GENERIC;
  }
  tzi_device_registry[tzi_device_registry_count++] =
    (tzi_device_registry_entry_t) {.name = name, .cbb = cbb};

  return TZ_SUCCESS;
}

extern void TVregister();

tz_return_t
TZDeviceOpen(IN void const *pkDeviceName,
             IN void const *pkInit,
             OUT tz_device_t *psDevice)
{
  int i;
  tz_return_t rv;
  static bool initialized = false;
  struct tzi_device_ext_t *psExt;

  /* temporary (?) hack. attempted to get device backends to register
     themselves with constructor functions, but they don't get linked
     in unless we reference symbols from them here. So we might as well
     just register them from here. */
  if(!initialized) {
    TVregister();
    initialized = true;
  }

  /* default device. currently hard-coded.
   * later consider taking an environment variable?
   */
  if (pkDeviceName == NULL) {
    pkDeviceName = "trustvisor";
  }

  /* linear search for requested device name */
  for(i=0; i < tzi_device_registry_count; i++) {
    if (strcmp(pkDeviceName, tzi_device_registry[i].name) == 0) {
      break;
    }
  }
  if (i >= tzi_device_registry_count) {
    return TZ_ERROR_ILLEGAL_ARGUMENT;
  }

  rv = tzi_device_registry[i].cbb->deviceOpen(pkDeviceName, pkInit, psDevice, &psExt);

  if (rv == TZ_SUCCESS) {
    *psDevice = (tz_device_t) {
      .uiState = TZ_STATE_OPEN,
      .sImp = {
        .cbb = tzi_device_registry[i].cbb,
        .uiSessionCount = 0,
        .psExt = psExt,
      },
    };
  } else {
    *psDevice = (tz_device_t) {
      .uiState = TZ_STATE_INVALID,
    };
  }

  return rv;
}

tz_return_t
TZDeviceClose(INOUT tz_device_t *psDevice)
{
  tz_return_t rv;
  if (psDevice->uiState == TZ_STATE_INVALID) {
    psDevice->uiState = TZ_STATE_UNDEFINED;

    return TZ_SUCCESS;
  } else if (psDevice->uiState != TZ_STATE_OPEN) {
    return TZ_ERROR_UNDEFINED;
  } else if (psDevice->sImp.uiSessionCount > 0) {
    return TZ_ERROR_ILLEGAL_STATE;
  }
  
  rv = psDevice->sImp.cbb->deviceClose(psDevice);
  if (rv == TZ_SUCCESS) {
    psDevice->uiState = TZ_STATE_UNDEFINED;
  }
  return rv;
}

tz_return_t
TZOperationPrepareOpen(INOUT tz_device_t* psDevice,
                       IN tz_uuid_t const * pksService,
                       IN tz_login_t const * pksLogin,
                       IN tz_timelimit_t const * pksTimeLimit,
                       OUT tz_session_t* psSession,
                       OUT tz_operation_t* psOperation)
{
  tz_return_t rv;
  struct tzi_session_ext_t *session_ext;
  struct tzi_operation_ext_t *operation_ext;
  tzi_encode_buffer_t *psEncodeBuf;
  uint32_t uiBufSize;

  if (psDevice == NULL
      || psDevice->uiState == TZ_STATE_INVALID
      || pksService == NULL
      || psSession == NULL
      || psOperation == NULL) {
    return TZ_ERROR_UNDEFINED;
  }

  rv = CBB_OF_DEVICE(psDevice)->operationPrepareOpen(psDevice,
                                                     pksService,
                                                     pksLogin,
                                                     pksTimeLimit,
                                                     &psEncodeBuf,
                                                     &uiBufSize,
                                                     &session_ext,
                                                     &operation_ext);

  if (rv == TZ_SUCCESS) {
    *psSession = (tz_session_t) {
      .uiState = TZ_STATE_INVALID,
      .sImp = {
        .psDevice = psDevice,
        .uiOpenOps = 1,
        .bManagerSession = false,
        .psExt = session_ext,
      }
    };

    assert(psEncodeBuf != NULL && uiBufSize >= sizeof(tzi_encode_buffer_t));
    *psEncodeBuf = (tzi_encode_buffer_t) {
      .uiRetVal = TZ_SUCCESS,
      .uiSize = uiBufSize - sizeof(tzi_encode_buffer_t),
      .uiOffset = 0,
    };

    *psOperation = (tz_operation_t) {
      .uiState = TZ_STATE_ENCODE,
      .sImp = {
        .psSession = psSession,
        .uiOpType = TZI_OPERATION_OPEN,
        .psEncodeBuffer = psEncodeBuf,
        .psExt = operation_ext,
      }
    };

    psDevice->sImp.uiSessionCount++;
  } else {
    *psSession = (tz_session_t) {
      .uiState = TZ_STATE_UNDEFINED
    };
    *psOperation = (tz_operation_t) {
      .uiState = TZ_STATE_INVALID
    };
  }

  return rv;
}

tz_return_t
TZOperationPrepareInvoke(INOUT tz_session_t* psSession,
                         uint32_t uiCommand,
                         IN tz_timelimit_t const * pksTimeLimit,
                         OUT tz_operation_t * psOperation)
{
  tz_return_t rv;
  struct tzi_operation_ext_t *psOperationExt;
  tzi_encode_buffer_t *psEncodeBuf;
  uint32_t uiBufSize;

  if (psSession == NULL
      || psSession->uiState != TZ_STATE_OPEN
      || psOperation == NULL) {
    return TZ_ERROR_UNDEFINED;
  }
  
  rv = CBB_OF_SESSION(psSession)->operationPrepareInvoke(psSession,
                                                         uiCommand,
                                                         pksTimeLimit,
                                                         &psEncodeBuf,
                                                         &uiBufSize,
                                                         &psOperationExt);

  if (rv == TZ_SUCCESS) {
    psSession->sImp.uiOpenOps++;

    assert(psEncodeBuf != NULL && uiBufSize >= sizeof(tzi_encode_buffer_t));
    *psEncodeBuf = (tzi_encode_buffer_t) {
      .uiRetVal = TZ_SUCCESS,
      .uiSize = uiBufSize - sizeof(tzi_encode_buffer_t),
      .uiOffset = 0,
    };

    *psOperation = (tz_operation_t) {
      .uiState = TZ_STATE_ENCODE,
      .sImp = {
        .psSession = psSession,
        .uiOpType = TZI_OPERATION_INVOKE,
        .psEncodeBuffer = psEncodeBuf,
        .psExt = psOperationExt,
      }
    };
  } else {
    *psOperation = (tz_operation_t) {
      .uiState = TZ_STATE_INVALID
    };
  }

  return rv;
}

tz_return_t
TZOperationPrepareClose(INOUT tz_session_t* psSession,
                        OUT tz_operation_t* psOperation)
{
  tz_return_t rv;
  struct tzi_operation_ext_t *psOperationExt;
  if (psSession == NULL
      || psSession->uiState != TZ_STATE_OPEN
      || psOperation == NULL) {
    return TZ_ERROR_UNDEFINED;
  }

  rv = CBB_OF_SESSION(psSession)->operationPrepareClose(psSession, &psOperationExt);

  if (rv == TZ_SUCCESS) {
    psSession->sImp.uiOpenOps++;
    psSession->uiState = TZ_STATE_CLOSING;

    *psOperation = (tz_operation_t) {
      .uiState = TZ_STATE_PERFORMABLE,
      .sImp = {
        .psSession = psSession,
        .uiOpType = TZI_OPERATION_CLOSE,
        .psExt = psOperationExt,
      }
    };
  } else {
    *psOperation = (tz_operation_t) {
      .uiState = TZ_STATE_INVALID
    };
  }
  return rv;
}

static void unreferenceSharedMemSubranges(INOUT tz_operation_t *psOperation)
{
  ll_t *refdSubranges=psOperation->sImp.psRefdSubranges;
  tzi_shared_memory_subrange_t *subrange;
  LL_FOR_EACH(refdSubranges, subrange) {
    /* remove self from the shared memory's list of referencing
       operations */
    LL_dremove(&subrange->psSharedMem->sImp.psRefdOperations, psOperation);
  }
  LL_free(psOperation->sImp.psRefdSubranges);
  psOperation->sImp.psRefdSubranges = NULL;
}

tz_return_t
TZOperationPerform(INOUT tz_operation_t* psOperation,
                   OUT tz_return_t* puiServiceReturn)
{
  tz_return_t rv;
  if (psOperation == NULL
      || !(psOperation->uiState == TZ_STATE_ENCODE
           || psOperation->uiState == TZ_STATE_PERFORMABLE)/* TZ_STATE_PERFORMABLE may also be acceptable. 6.1.7 contradicts itself */
      || (psOperation->sImp.uiOpType == TZI_OPERATION_CLOSE
          && (psOperation->sImp.psSession->sImp.uiOpenOps > 1
              || psOperation->sImp.psSession->sImp.uiOpenSharedMem > 0))
      || puiServiceReturn == NULL) {
    return TZ_ERROR_UNDEFINED;
  }

  if (psOperation->sImp.psEncodeBuffer != NULL
      && psOperation->sImp.psEncodeBuffer->uiRetVal != TZ_SUCCESS) {
    *puiServiceReturn = TZ_ERROR_GENERIC;
    psOperation->uiState = TZ_STATE_INVALID;
    return psOperation->sImp.psEncodeBuffer->uiRetVal;
  }

  rv = CBB_OF_OPERATION(psOperation)->operationPerform(psOperation, puiServiceReturn);

  /* cf 6.2.4 */
  unreferenceSharedMemSubranges(psOperation);

  /* check for encoder errors caused by the service */
  if (psOperation->sImp.psEncodeBuffer != NULL
      && psOperation->sImp.psEncodeBuffer->uiRetVal != TZ_SUCCESS) {
    *puiServiceReturn = TZ_ERROR_GENERIC;
    psOperation->uiState = TZ_STATE_INVALID;
    rv = psOperation->sImp.psEncodeBuffer->uiRetVal;
  }

  /* enforce spec post-conditions */
  if (rv == TZ_SUCCESS) {
    *puiServiceReturn = TZ_SUCCESS;
  }
  switch (psOperation->sImp.uiOpType) {
  case TZI_OPERATION_OPEN:
    if (rv == TZ_SUCCESS) {
      psOperation->sImp.psSession->uiState = TZ_STATE_OPEN;
      psOperation->uiState = TZ_STATE_DECODE;
      /* note that device session count was already incremented
         in TZOperationPrepareOpen */
    }
    break;
  case TZI_OPERATION_INVOKE:
    if (rv == TZ_SUCCESS) {
      psOperation->uiState = TZ_STATE_DECODE;
    } else if (rv == TZ_ERROR_SERVICE) {
      psOperation->uiState = TZ_STATE_DECODE;
    } else {
      psOperation->uiState = TZ_STATE_INVALID;
    }
    break;
  case TZI_OPERATION_CLOSE:
    psOperation->uiState = TZ_STATE_INVALID;

    /* session is considered closed regardless of rv */
    psOperation->sImp.psSession->uiState = TZ_STATE_INVALID;
    psOperation->sImp.psSession->sImp.psDevice->sImp.uiSessionCount--;
    break;
  default:
    return TZ_ERROR_UNDEFINED;
  }
  return rv;
}

void
TZOperationRelease(INOUT tz_operation_t* psOperation)
{
  if (psOperation == NULL
      || !(psOperation->uiState == TZ_STATE_ENCODE
           || psOperation->uiState == TZ_STATE_PERFORMABLE
           || psOperation->uiState == TZ_STATE_DECODE
           || psOperation->uiState == TZ_STATE_INVALID)) {
    return; /* undefined behavior */
  }

  /* cf 6.2.4 */
  unreferenceSharedMemSubranges(psOperation);

  /* any cleanup should already be done when
   * transition to TZ_STATE_INVALID occurred 
   * FIXME- revisit this
   */
  if (psOperation->uiState == TZ_STATE_INVALID) {
    return; /* no-op */
  }

  CBB_OF_OPERATION(psOperation)->operationRelease(psOperation);

  /* unwind un-issued operations */
  /* FIXME is the state TZ_STATE_ENCODE or TZ_STATE_PEFORMABLE
     iff the operation is un-issued?
  */
  if((psOperation->uiState == TZ_STATE_ENCODE
      || psOperation->uiState == TZ_STATE_PERFORMABLE)) {
    switch (psOperation->sImp.uiOpType) {
    case TZI_OPERATION_OPEN:
      psOperation->sImp.psSession->sImp.psDevice->sImp.uiSessionCount--;
      break;
    case TZI_OPERATION_INVOKE:
      break;
    case TZI_OPERATION_CLOSE:
      psOperation->sImp.psSession->uiState = TZ_STATE_OPEN;
      break;
    }
  }
  /* FIXME will need to clean up marshalling, shared mem, etc. */

  psOperation->sImp.psSession->sImp.uiOpenOps--;
}

static bool bits_are_subset_of(uint32_t child, uint32_t parent)
{
  return ((child & ~parent) == 0);
}

tz_return_t
TZSharedMemoryAllocate(INOUT tz_session_t* psSession,
                       INOUT tz_shared_memory_t* psSharedMem)
{
  tz_return_t rv;

  if (psSession == NULL
      || psSession->uiState != TZ_STATE_OPEN
      || psSharedMem == NULL
      || !bits_are_subset_of(psSharedMem->uiFlags, TZ_MEM_SERVICE_RW)
      || psSharedMem->uiLength == 0) {
    return TZ_ERROR_UNDEFINED;
  }

  rv = CBB_OF_SESSION(psSession)->sharedMemoryAllocate(psSession,
                                                       psSharedMem);

  if(rv == TZ_SUCCESS) {
    assert((uint32_t)(psSharedMem->pBlock) % 8 == 0); /* TZ spec requirement */
    psSharedMem->uiState = TZ_STATE_OPEN;
    psSharedMem->sImp.psSession = psSession;
    psSession->sImp.uiOpenSharedMem++;
    psSharedMem->sImp.bAllocated = true;
  } else {
    assert(psSharedMem->pBlock == NULL);
    psSharedMem->uiState = TZ_STATE_INVALID;
    psSharedMem->sImp.psSession = NULL;
  }

  return rv;
}

tz_return_t
TZSharedMemoryRegister(INOUT tz_session_t* psSession,
                       INOUT tz_shared_memory_t* psSharedMem)
{
  tz_return_t rv;

  if (psSession == NULL
      || psSession->uiState != TZ_STATE_OPEN
      || psSharedMem == NULL
      || psSharedMem->pBlock == NULL
      || !bits_are_subset_of(psSharedMem->uiFlags, TZ_MEM_SERVICE_RW)
      || psSharedMem->uiFlags == 0) {
    return TZ_ERROR_UNDEFINED;
  }

  rv = CBB_OF_SESSION(psSession)->sharedMemoryRegister(psSession,
                                                       psSharedMem);

  if(rv == TZ_SUCCESS) {
    psSharedMem->uiState = TZ_STATE_OPEN;
    psSharedMem->sImp.bAllocated = false;
    psSession->sImp.uiOpenSharedMem++;
  } else {
    psSharedMem->uiState = TZ_STATE_INVALID;
  }

  return rv;
}

void
TZSharedMemoryRelease(INOUT tz_shared_memory_t* psSharedMem)
{
  if (psSharedMem == NULL
      || psSharedMem->sImp.psRefdOperations != NULL) {
    /* FIXME undefined behavior. print a warning? */
    return;
  }

  if (psSharedMem->uiState != TZ_STATE_INVALID) {
    CBB_OF_SHAREDMEM(psSharedMem)->sharedMemoryRelease(psSharedMem);
    psSharedMem->sImp.psSession->sImp.uiOpenSharedMem--;
  }

  psSharedMem->uiState = TZ_STATE_UNDEFINED;
  psSharedMem->pBlock = NULL; /* not required by spec, but good for debugging */
}


void
TZEncodeUint32(INOUT tz_operation_t* psOperation,
               uint32_t uiData)
{
  TZIEncodeUint32(psOperation->sImp.psEncodeBuffer,
                  uiData);
}
uint32_t
TZDecodeUint32(INOUT tz_operation_t* psOperation)
{
  return TZIDecodeUint32(psOperation->sImp.psEncodeBuffer);
}


void
TZEncodeArray(INOUT tz_operation_t* psOperation,
              IN void const * pkArray,
              uint32_t uiLength)
{
  TZIEncodeArray(psOperation->sImp.psEncodeBuffer,
                 pkArray,
                 uiLength);
}

void* 
TZEncodeArraySpace(INOUT tz_operation_t* psOperation,
                   uint32_t uiLength)
{
  return TZIEncodeArraySpace(psOperation->sImp.psEncodeBuffer,
                             uiLength);
}

void *
TZDecodeArraySpace(INOUT tz_operation_t* psOperation,
                   OUT uint32_t* puiLength)
{
  return TZIDecodeArraySpace(psOperation->sImp.psEncodeBuffer,
                             puiLength);
}

static bool ranges_overlap(uint32_t start1, uint32_t length1,
                           uint32_t start2, uint32_t length2)
{
  uint32_t end1 = start1+length1-1;
  uint32_t end2 = start2+length2-1;

  /* break into 3 cases: start2 is before, in, or after first range */
  if (start2 < start1) {
    /* before */
    return (end2 >= start1);
  } else if (start2 >= start1 && start2 <= end1) {
    /* in */
    return true;
  } else {
    /* after */
    return false;
  }
}

static bool range_already_referenced(IN tz_shared_memory_t *psSharedMem,
                                     uint32_t uiOffset,
                                     uint32_t uiLength)
{
  ll_t *ops_l = psSharedMem->sImp.psRefdOperations;
  tz_operation_t *op = NULL;
  LL_FOR_EACH(ops_l, op) {
    ll_t *range_l = op->sImp.psRefdSubranges;
    tzi_shared_memory_subrange_t *subrange = NULL;
    LL_FOR_EACH(range_l, subrange) {
      if (ranges_overlap(uiOffset, uiLength,
                         subrange->uiOffset, subrange->uiLength)) {
        return true;
      }
    }
  }
  return false;
}

void
TZEncodeMemoryReference(INOUT tz_operation_t* psOperation,
                        INOUT tz_shared_memory_t* psSharedMem,
                        uint32_t uiOffset,
                        uint32_t uiLength,
                        uint32_t uiFlags)
{
  uint32_t uiEncodeOffset;
  tzi_shared_memory_subrange_t *psSubrange=NULL;

  if (psOperation == NULL
      || psOperation->uiState != TZ_STATE_ENCODE
      || psSharedMem == NULL
      || psSharedMem->uiState != TZ_STATE_OPEN) {
    return; /* FIXME print warning? */
  }

  /* check for encode_format errors, as per spec */
  if ((uiOffset+uiLength) > psSharedMem->uiLength
      || !bits_are_subset_of(uiFlags, psSharedMem->uiFlags)
      || range_already_referenced(psSharedMem, uiOffset, uiLength)) {
    psOperation->sImp.psEncodeBuffer->uiRetVal = TZ_ERROR_ENCODE_FORMAT;
    return;
  }

  /* encoder just needs address and length. returns offset (into the
   * encode-buffer) of the encoded address so that device back-end can
   * rewrite it if necessary. (address space of trusted environment
   * may not be unity-mapped with address space of caller)
   */
  uiEncodeOffset = TZIEncodeMemoryReference(psOperation->sImp.psEncodeBuffer,
                                            psSharedMem->pBlock+uiOffset,
                                            uiLength);

  /* silently return if encoder is in an error state,
     whether caused previously or just now */
  if (psOperation->sImp.psEncodeBuffer->uiRetVal != TZ_SUCCESS) {
    return;
  }

  /* malloc and init new subrange struct */
  psSubrange = malloc(sizeof(*psSubrange));
  if (psSubrange == NULL) {
    /* using TZ_ERROR_MEMORY instead of TZ_ERROR_ENCODE_MEMORY, to
       distinguish from case where encode buffer itself wasn't large
       enough */
    psOperation->sImp.psEncodeBuffer->uiRetVal = TZ_ERROR_MEMORY; 
    return;
  }
  *psSubrange = (tzi_shared_memory_subrange_t) {
    .psSharedMem = psSharedMem,
    .uiOffset = uiOffset,
    .uiLength = uiLength,
    .uiFlags = uiFlags,
    .uiEncodeOffset = uiEncodeOffset
  };

  /* add to operation's list of referenced subranges */
  if (LL_dpush(&psOperation->sImp.psRefdSubranges, psSubrange) == NULL) {
    psOperation->sImp.psEncodeBuffer->uiRetVal = TZ_ERROR_MEMORY; 
    return;
  }

  /* add this operation to psSharedMem's list of referencing
   * operations, if not already there. */
  /* XXX horribly inefficient if we have a large number of
     open operations referencing a psSharedMem */
  {
    ll_t *l = psSharedMem->sImp.psRefdOperations;
    tz_operation_t *op = NULL;
    LL_FOR_EACH(l, op) {
      if (op == psOperation) {
        break;
      }
    }
    if (l == NULL) { /* not found */
      if (LL_dpush(&psSharedMem->sImp.psRefdOperations,
                   psOperation) == NULL) {
        psOperation->sImp.psEncodeBuffer->uiRetVal = TZ_ERROR_MEMORY;
        return;
      }
    }
  }
}

tz_return_t
vTZIEncodeF(INOUT tz_operation_t *psOperation, const char* str, va_list argp)
{
  return vTZIEncodeBufF(psOperation->sImp.psEncodeBuffer, str, argp);
}

tz_return_t
TZIEncodeF(INOUT tz_operation_t *psOperation, const char* str, ...)
{
  tz_return_t rv;
  va_list argp;
  va_start(argp, str);
  rv = vTZIEncodeF(psOperation, str, argp);
  va_end(argp);
  return rv;
}

tz_return_t
vTZIDecodeF(INOUT tz_operation_t *psOperation, const char* str, va_list argp)
{
  return vTZIDecodeBufF(psOperation->sImp.psEncodeBuffer, str, argp);
}

tz_return_t
TZIDecodeF(INOUT tz_operation_t *psOperation, const char* str, ...)
{
  tz_return_t rv;
  va_list argp;
  va_start(argp, str);
  rv = vTZIDecodeF(psOperation, str, argp);
  va_end(argp);
  return rv;
}

tz_return_t
TZDecodeGetError(INOUT tz_operation_t * psOperation)
{
  return TZIDecodeGetError(psOperation->sImp.psEncodeBuffer);
}

tz_return_t
TZManagerOpen(INOUT tz_device_t* psDevice,
              IN tz_login_t const * pksLogin,
              OUT tz_session_t* psSession)
{
  tz_return_t rv;
  struct tzi_session_ext_t* psExt;

  if (psDevice == NULL
      || psDevice->uiState != TZ_STATE_OPEN
      || psSession == NULL) {
    psSession->uiState = TZ_STATE_INVALID;
    return TZ_ERROR_UNDEFINED;
  }

  rv = CBB_OF_DEVICE(psDevice)->managerOpen(psDevice, pksLogin, &psExt);

  if (rv == TZ_SUCCESS) {
    *psSession = (tz_session_t) {
      .uiState = TZ_STATE_OPEN,
      .sImp = {
        .psDevice = psDevice,
        .uiOpenOps = 0,
        .bManagerSession = true,
        .psExt = psExt,
      }
    };
    psDevice->sImp.uiSessionCount++;
  } else {
    *psSession = (tz_session_t) {
      .uiState = TZ_STATE_INVALID,
    };
  }

  return rv;
}

tz_return_t
TZManagerClose(INOUT tz_session_t* psSession)
{
  tz_return_t rv;

  if (psSession == NULL) {
    return TZ_ERROR_UNDEFINED;
  }
  if (!psSession->sImp.bManagerSession) {
    /* session is not with Manager */
    return TZ_ERROR_UNDEFINED;
  }
  if (psSession->uiState == TZ_STATE_INVALID) {
    /* according to TZ spec- silently succeed */
    return TZ_SUCCESS;
  }
  if (psSession->uiState != TZ_STATE_OPEN) {
    return TZ_ERROR_UNDEFINED;
  }

  /* FIXME- according to spec, need to cancel any operations pending
     on service manager. Should we do it at this layer by keeping
     track of open operations on a session and here calling
     TZOperationCancel on each one?
  */

  rv = CBB_OF_SESSION(psSession)->managerClose(psSession);

  /* spec guarantees that session is closed when this function returns,
     even if returning an error. Therefore unconditionally close:
  */
  psSession->sImp.psDevice->sImp.uiSessionCount--;
  psSession->uiState = TZ_STATE_UNDEFINED;

  return TZ_SUCCESS;
}

tz_return_t
TZManagerDownloadService(INOUT tz_session_t* psSession,
                         IN void const * kauiData,
                         uint32_t uiLength,
                         OUT tz_uuid_t* psServiceId)
{
  
  /* ensure basic parameter validity */
  {
    if (psSession == NULL
        || psSession->uiState == TZ_STATE_INVALID
        || !psSession->sImp.bManagerSession
        || kauiData == NULL) {
      return TZ_ERROR_UNDEFINED;
    }
  }

  return CBB_OF_SESSION(psSession)->downloadService(psSession,
                                                    kauiData, uiLength,
                                                    psServiceId);
}

tz_return_t
TZManagerRemoveService(INOUT tz_session_t* psSession,
                       IN tz_uuid_t const * pksService)
{
  /* ensure basic param validity */
  {
    if (psSession == NULL
        || psSession->uiState == TZ_STATE_INVALID
        || !psSession->sImp.bManagerSession
        || pksService == NULL) {
      return TZ_ERROR_UNDEFINED;
    }
  }

  return CBB_OF_SESSION(psSession)->removeService(psSession, pksService);
}
