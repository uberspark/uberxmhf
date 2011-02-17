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

#include <tv.h>
#include <marshal.h>

#include <string.h>
#include <stdlib.h>
#include <assert.h>

#include "scode.h"

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

/* temporary hard-coded size of marshal buffer */
#define MARSHAL_BUF_SIZE 1000

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
  posix_memalign((void**)ppsBufData, 8, *puiBufSize);
  *ppsSessionExt = malloc(sizeof(tzi_session_ext_t));
  *ppsOperationExt = NULL;
  if (*ppsBufData == NULL || *ppsSessionExt == NULL) {
    free(*ppsBufData);
    free(*ppsSessionExt);
    return TZ_ERROR_MEMORY;
  }

  (*ppsSessionExt)->pFn = *((pal_fn_t*)pksService);

  return TZ_SUCCESS;
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

      posix_memalign((void**)&psOutBuf, 8, MARSHAL_BUF_SIZE);
      if(psOutBuf == NULL) {
        return TZ_ERROR_MEMORY;
      }
      TZIEncodeBufInit(psOutBuf, MARSHAL_BUF_SIZE);

      TZIEncodeToDecode(psInBuf);
      fn(uiCommand, psInBuf, psOutBuf, puiServiceReturn);
      TZIEncodeToDecode(psOutBuf);

      free(psInBuf);
      psOperation->sImp.psEncodeBuffer = psOutBuf;

      if (*puiServiceReturn != TZ_SUCCESS) {
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
  posix_memalign((void**)ppsBufData, 8, *puiBufSize);
  *ppsOperationExt = malloc(sizeof(tzi_operation_invoke_ext_t));
  if (*ppsBufData == NULL || *ppsOperationExt == NULL) {
    free(*ppsBufData);
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
  free(psOperation->sImp.psEncodeBuffer);
  return;
}

tz_return_t
TVDeviceOpen(IN void const *pkDeviceName,
             IN void const *pkInit,
             OUT tz_device_t *psDevice)
{
  assert(strcmp(pkDeviceName, "trustvisor") == 0);

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

  struct scode_params_info params = 
    { 
      .params_num = 4,
      .pm_str =
      {
        /* uiCommand */
        {.type = SCODE_PARAM_TYPE_INTEGER,
         .size = sizeof(uint32_t)/sizeof(int)},

        /* psInBuf */
        {.type = SCODE_PARAM_TYPE_POINTER,
         .size = MARSHAL_BUF_SIZE/sizeof(int)},

        /* psOutBuf */
        {.type = SCODE_PARAM_TYPE_POINTER,
         .size = MARSHAL_BUF_SIZE/sizeof(int)},

        /* puiRv */
        {.type = SCODE_PARAM_TYPE_POINTER,
         .size = sizeof(uint32_t)/sizeof(int)}
      }
    };
  rv = scode_register(svc->sPageInfo,
                      &params,
                      svc->pEntry);
  if (rv != 0) {
    return TZ_ERROR_GENERIC;
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
  /* FIXME- need to make sure there's no open sessions */
  if(scode_unregister(*((pal_fn_t*)(pksService))) != 0)
    return TZ_ERROR_GENERIC;

  return TZ_SUCCESS;
}

tzi_device_cb_block_t tv_cb_block =
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
  };

