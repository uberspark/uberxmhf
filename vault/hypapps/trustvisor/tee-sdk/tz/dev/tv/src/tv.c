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

#include <stdbool.h>

#include <tv.h>
#include <tzmarshal.h>
#include <list.h>

#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>

#include <tz_platform.h>

typedef struct tzi_session_ext_t {
  pal_fn_t pFn;
} tzi_session_ext_t;

typedef struct tzi_operation_open_ext_t {
} tzi_operation_open_ext_t;
typedef struct tzi_operation_invoke_ext_t {
  uint32_t uiCommand;
} tzi_operation_invoke_ext_t;
typedef struct tzi_operation_close_ext_t {
} tzi_operation_close_ext_t;

typedef struct tzi_device_ext_t {
  bool userspace_only;
} tzi_device_ext_t;

/* temporary hard-coded size of marshal buffer */
#define MARSHAL_BUF_SIZE (1*PAGE_SIZE_4K)

tz_return_t
TVOperationPrepareOpen(INOUT tz_device_t* psDevice,
                       IN tz_uuid_t const * pksService,
                       IN tz_login_t const * pksLogin,
                       IN tz_timelimit_t const * pksTimeLimit,
                       OUT tzi_encoded_t **ppsBufData,
                       OUT uint32_t *puiBufSize,
                       OUT tzi_session_ext_t** ppsSessionExt,
                       OUT tzi_operation_open_ext_t** ppsOperationExt)
{

  /* XXX later we'll point to a page to be re-mapped instead of
     copied */
  *puiBufSize = MARSHAL_BUF_SIZE;
  *ppsBufData = tz_aligned_malloc( *puiBufSize, PAGE_SIZE_4K);
  *ppsSessionExt = malloc(sizeof(tzi_session_ext_t));
  *ppsOperationExt = NULL;
  if (*ppsBufData == NULL || *ppsSessionExt == NULL) {
    tz_aligned_free( *ppsBufData);
    free(*ppsSessionExt);
    return TZ_ERROR_MEMORY;
  }

  (*ppsSessionExt)->pFn = *((pal_fn_t*)pksService);

  return TZ_SUCCESS;
}

static int share_referenced_mem(pal_fn_t fn, ll_t* psRefdSubranges, void* psOutBuf, void* psInBuf, bool userspace_only,
                                void ***addrs, size_t **lens, size_t *count)
{
  tzi_shared_memory_subrange_t *subrange;
  int i;
  int rv=0;

  *addrs = NULL;
  *lens = NULL;

  *count=2; /* psOutBuf and psInBuf */
  LL_FOR_EACH(psRefdSubranges, subrange) {
    (*count)++;
  }

  *addrs = calloc(*count, sizeof(void*));
  *lens = calloc(*count, sizeof(size_t));
  
  (*addrs)[0] = psOutBuf;
  (*lens)[0] = MARSHAL_BUF_SIZE;
  (*addrs)[1] = psInBuf;
  (*lens)[1] = MARSHAL_BUF_SIZE;

  i=2;
  LL_FOR_EACH(psRefdSubranges, subrange) {
    (*addrs)[i] = subrange->psSharedMem->pBlock + subrange->uiOffset;
    (*lens)[i] = subrange->uiLength;
    if(!PAGE_ALIGNED_4K((uintptr_t)(*addrs)[i]) || !PAGE_ALIGNED_4K((*lens)[i])) {
      printf("Error: TV back-end currently only supports 4K-aligned shared memory subranges\n");
      goto out;
    }
    i++;
  }

  for(i=0; i<*count; i++) {
    tv_lock_range((*addrs)[i], (*lens)[i]);
    tv_touch_range((*addrs)[i], (*lens)[i], true);
  }

  if(!userspace_only)
    rv = tv_pal_share(fn, (*addrs), (*lens), *count);

  /* XXX we currently do not enforce the specified permissions-
     the service (pal) gets full access */

 out:
  if(rv) {
    free(*addrs);
    *addrs=NULL;
    free(*lens);
    *lens=NULL;
  }
  return rv;
}

static int unshare_referenced_mem(void **addrs, size_t *lens, size_t count)
{
  int i;
  int rv=0;

  for(i=0; i<count; i++) {
    tv_unlock_range(addrs[i], lens[i]);
  }

 out:
  free(addrs);
  free(lens);
  return rv;
}

tz_return_t
TVOperationPerform(INOUT tz_operation_t* psOperation,
                   OUT tz_return_t* puiServiceReturn)
{
  switch(psOperation->sImp.uiOpType) {
  case TZI_OPERATION_OPEN:
    return TZ_SUCCESS;
    break;
  case TZI_OPERATION_INVOKE:
    {
      tzi_operation_invoke_ext_t *psExt = (tzi_operation_invoke_ext_t*)psOperation->sImp.psExt;
      pal_fn_t fn =  psOperation->sImp.psSession->sImp.psExt->pFn;
      uint32_t uiCommand = psExt->uiCommand;
      tzi_encode_buffer_t *psInBuf = psOperation->sImp.psEncodeBuffer;
      tzi_encode_buffer_t *psOutBuf = NULL;
      void **shared_addrs=NULL;
      size_t *shared_lens=NULL;
      size_t shared_count=0;

      psOutBuf = tz_aligned_malloc( MARSHAL_BUF_SIZE, PAGE_SIZE_4K);
      if(psOutBuf == NULL) {
        return TZ_ERROR_MEMORY;
      }
      TZIEncodeBufInit(psOutBuf, MARSHAL_BUF_SIZE);

      TZIEncodeToDecode(psInBuf);

      if (share_referenced_mem(fn,
                               psOperation->sImp.psRefdSubranges,
                               psOutBuf,
                               psInBuf,
                               psOperation->sImp.psSession->sImp.psDevice->sImp.psExt->userspace_only,
                               &shared_addrs,
                               &shared_lens,
                               &shared_count)) {
        return TZ_ERROR_GENERIC;
      }
      fn(uiCommand, psInBuf, psOutBuf, puiServiceReturn);
      unshare_referenced_mem(shared_addrs, shared_lens, shared_count);

      TZIEncodeToDecode(psOutBuf);

      tz_aligned_free(psInBuf);
      psOperation->sImp.psEncodeBuffer = psOutBuf;

      if (*puiServiceReturn != TZ_SUCCESS) {
          printf("[tee-sdk] Failure in %s (*puiServiceReturn = 0x%08x) in %s:%d\n",
                 __FUNCTION__, *puiServiceReturn, __FILE__, __LINE__);
        return TZ_ERROR_SERVICE;
      }
      return TZ_SUCCESS;
    }
    break;
  case TZI_OPERATION_CLOSE:
    return TZ_SUCCESS;
    break;
  default:
    return TZ_ERROR_NOT_IMPLEMENTED;
  }
}

tz_return_t
TVOperationPrepareInvoke(INOUT tz_session_t* psSession,
                         uint32_t uiCommand,
                         IN tz_timelimit_t const * pksTimeLimit,
                         OUT tzi_encoded_t **ppsBufData,
                         OUT uint32_t *puiBufSize,
                         OUT tzi_operation_invoke_ext_t** ppsOperationExt)
{
 /* XXX later we'll point to a page to be re-mapped instead of
    copied */
  *puiBufSize = MARSHAL_BUF_SIZE;
  *ppsBufData = tz_aligned_malloc( *puiBufSize, PAGE_SIZE_4K);
  *ppsOperationExt = malloc(sizeof(tzi_operation_invoke_ext_t));
  if (*ppsBufData == NULL || *ppsOperationExt == NULL) {
    tz_aligned_free( *ppsBufData);
    free(*ppsOperationExt);
    return TZ_ERROR_MEMORY;
  }

  (*ppsOperationExt)->uiCommand = uiCommand;

  return TZ_SUCCESS;
}

tz_return_t
TVOperationPrepareClose(INOUT tz_session_t* psSession,
                        OUT tzi_operation_close_ext_t** ppsOperationExt)
{
  *ppsOperationExt = NULL;
  return TZ_SUCCESS;
}


void
TVOperationRelease(INOUT tz_operation_t* psOperation)
{
  free(psOperation->sImp.psExt);
  tz_aligned_free( psOperation->sImp.psEncodeBuffer);
  return;
}

tz_return_t
TVDeviceOpen(IN void const *pkDeviceName,
             IN void const *pkInit,
             OUT tz_device_t *psDevice,
             OUT tzi_device_ext_t **psExt)
{
  const tv_device_open_options_t *options;
  const tv_device_open_options_t default_options =
    (tv_device_open_options_t) {
    .userspace_only = false,
  };
  if (pkInit) {
    options = (const tv_device_open_options_t*)pkInit;
  } else {
    options = &default_options;
  }

  *psExt = malloc(sizeof(tzi_device_ext_t));
  if (!*psExt) {
    return TZ_ERROR_MEMORY;
  }

  (*psExt)->userspace_only = options->userspace_only;

  assert(!strcmp(pkDeviceName, "trustvisor"));

  return TZ_SUCCESS;
}

tz_return_t
TVDeviceClose(INOUT tz_device_t *psDevice)
{
  return TZ_SUCCESS;
}

tz_return_t
TVManagerOpen(INOUT tz_device_t* psDevice,
              IN tz_login_t const * pksLogin,
              OUT tzi_session_ext_t** psSession)
{
  *psSession = NULL;
  return TZ_SUCCESS;
}

tz_return_t
TVManagerClose(INOUT tz_session_t* psSession)
{
  return TZ_SUCCESS;
}

tz_return_t
TVManagerDownloadService(INOUT tz_session_t* psSession,
                         IN uint8_t const * kauiData,
                         uint32_t uiLength,
                         OUT tz_uuid_t* psService)
{
  const tv_service_t *svc = (tv_service_t*) kauiData;
  int rv;

  struct tv_pal_params params = 
    { 
      .num_params = 4,
      .params =
      {
        /* uiCommand */
        {.type = TV_PAL_PM_INTEGER,
         .size = sizeof(uint32_t)/sizeof(int)},

        /* psInBuf. (pass a pointer to a shared region) */
        {.type = TV_PAL_PM_INTEGER,
         .size = sizeof(uint32_t)/sizeof(int)},

        /* psOutBuf */
        {.type = TV_PAL_PM_INTEGER,
         .size = sizeof(uint32_t)/sizeof(int)},

        /* puiRv */
        {.type = TV_PAL_PM_POINTER,
         .size = sizeof(uint32_t)/sizeof(int)}
      }
    };

  if (!psSession->sImp.psDevice->sImp.psExt->userspace_only) {
    tv_lock_pal_sections(svc->sPageInfo);

    rv = tv_pal_register(svc->sPageInfo,
                         &params,
                         svc->pEntry);
  
    if (rv != 0) {
      return TZ_ERROR_GENERIC;
    }
  }

  /* for now we just shove the function ptr into
   * the uuid. once we're using proper uuid's we'll
   * need to maintain a uuid -> function ptr mapping.
   */
  *((pal_fn_t*)psService) = svc->pEntry;

  return TZ_SUCCESS;
}

tz_return_t
TVManagerRemoveService(INOUT tz_session_t* psSession,
                       IN tz_uuid_t const * pksService)
{
  if (!psSession->sImp.psDevice->sImp.psExt->userspace_only) {
    /* FIXME- need to make sure there's no open sessions */
    if(tv_pal_unregister(*((pal_fn_t*)(pksService))) != 0)
      return TZ_ERROR_GENERIC;
  }

  return TZ_SUCCESS;
}

tz_return_t TVsharedMemoryAllocate(INOUT tz_session_t* psSession,
                                   INOUT tz_shared_memory_t* psSharedMem)
{
  if ( !( psSharedMem->pBlock = tz_aligned_malloc( PAGE_ALIGN_UP4K( psSharedMem->uiLength),
                                                   PAGE_SIZE_4K))) {
    return TZ_ERROR_MEMORY;
  }
  return TZ_SUCCESS;
}

tz_return_t TVsharedMemoryRegister(INOUT tz_session_t* psSession,
                                   INOUT tz_shared_memory_t* psSharedMem)
{
  if (!PAGE_ALIGNED_4K((uintptr_t)psSharedMem->pBlock)
      || !PAGE_ALIGNED_4K(psSharedMem->uiLength)) {
    /* we only handle aligned regions right now */
    return TZ_ERROR_ILLEGAL_ARGUMENT;
  } else {
    return TZ_SUCCESS;
  }
}

void TVsharedMemoryRelease(INOUT tz_shared_memory_t* psSharedMem)
{
  if(psSharedMem->sImp.bAllocated) {
    tz_aligned_free( psSharedMem->pBlock);
  }
  psSharedMem->pBlock=NULL;
  return;
}

static tzi_device_cb_block_t tv_cb_block =
  { &TVDeviceOpen,
    &TVDeviceClose, 
    &TVManagerOpen,
    &TVManagerClose,
    &TVManagerDownloadService, 
    &TVManagerRemoveService,
    &TVOperationPrepareOpen,
    &TVOperationPrepareInvoke,
    &TVOperationPrepareClose,
    &TVOperationPerform,
    &TVOperationRelease,
    &TVsharedMemoryAllocate,
    &TVsharedMemoryRegister,
    &TVsharedMemoryRelease,
  };

void TVregister()
{
  TZIDeviceRegister("trustvisor", &tv_cb_block);
}
