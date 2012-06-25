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

#ifndef TZ_H
#define TZ_H

#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdarg.h>

/* implementation features.
 * define iff the implementation implements the corresponding feature.
 * [TZS] 5.5.1
 */
#define TZ_BUILD_RUNTIME_SERVICE_CONTROL
#undef TZ_BUILD_ASYNCHRONOUS 
#undef TZ_BUILD_MULTITHREADS 

/* 5.3.1 */
typedef uint32_t tz_return_t;

/* 5.3.2 */
typedef uint32_t tz_state_t;

/* 5.3.3 */
typedef struct
{
  uint32_t uiTimeLow;
  uint16_t uiTimeMid;
  uint16_t uiTimeHiAndVersion;
  uint8_t auiClockSeqAndNode[8];
} tz_uuid_t;

/* 5.3.4 */
typedef struct
{
  uint32_t uiType;
  void *pBuff;
  uint32_t uiBuffLen;
} tz_login_t;

/* 5.3.5 */
typedef struct tz_property_t
{
  uint32_t uiNamespace;
  uint32_t uiName;
  void *pValue;
  uint32_t uiLength;
} tz_property_t;

/* 5.3.6 */
typedef struct tz_property_name_t
{
  uint32_t uiNamespace;
  uint32_t uiName;
} tz_property_name_t;

/* 5.4.1 */
typedef struct tz_timelimit_t
{
  /* Implementation-defined. */
} tz_timelimit_t;

typedef struct tzi_device_cb_block_t {
  tz_return_t (*deviceOpen)();
  tz_return_t (*deviceClose)();
  tz_return_t (*managerOpen)();
  tz_return_t (*managerClose)();
  tz_return_t (*downloadService)();
  tz_return_t (*removeService)();
  tz_return_t (*operationPrepareOpen)();
  tz_return_t (*operationPrepareInvoke)();
  tz_return_t (*operationPrepareClose)();
  tz_return_t (*operationPerform)();
  void (*operationRelease)();
  tz_return_t (*sharedMemoryAllocate)();
  tz_return_t (*sharedMemoryRegister)();
  void (*sharedMemoryRelease)();
} tzi_device_cb_block_t;

typedef struct tzi_device_registry_entry_t {
  const char* name;
  tzi_device_cb_block_t* cbb;
} tzi_device_registry_entry_t;

/* 5.4.2 */
typedef struct tz_device_t
{
  tz_state_t uiState;
  struct
  {
    /* Implementation-defined. */
    const tzi_device_cb_block_t *cbb;
    struct tzi_device_ext_t* psExt;
    uint32_t uiSessionCount;
  } sImp;
} tz_device_t;

/* 5.4.3 */
typedef struct tz_session_t
{
  tz_state_t uiState;
  struct
  {
    /* Implementation-defined. */
    tz_device_t* psDevice;
    uint32_t uiOpenOps;
    uint32_t uiOpenSharedMem;
    bool bManagerSession;
    struct tzi_session_ext_t* psExt;
  } sImp;
} tz_session_t;

typedef enum {
  TZI_OPERATION_OPEN,
  TZI_OPERATION_INVOKE,
  TZI_OPERATION_CLOSE,
} tzi_operation_t;

/* used to keep track of referenced memory ranges in a
   tz_shared_memory_t */
typedef struct tzi_shared_memory_subrange_t
{
  struct tz_shared_memory_t *psSharedMem;
  uint32_t uiOffset;
  uint32_t uiLength;
  uint32_t uiFlags;
  uint32_t uiEncodeOffset;
} tzi_shared_memory_subrange_t;

/* 5.4.4 */
typedef struct tz_operation_t
{
  tz_state_t uiState;
  struct
  {
    /* Implementation-defined. */
    tz_session_t *psSession;
    tzi_operation_t uiOpType;
    struct tzi_encode_buffer_t *psEncodeBuffer;
    struct tzi_operation_ext_t* psExt;
    struct ll_t* psRefdSubranges;
  } sImp;
} tz_operation_t;

/* 5.4.5 */
typedef struct tz_shared_memory_t
{
  tz_state_t uiState;
  uint32_t uiLength;
  uint32_t uiFlags;
  void* pBlock;
  struct
  {
    /* Implementation-defined. */
    tz_session_t *psSession;
    struct ll_t* psRefdOperations;
    bool bAllocated; /* true if initd through TZSharedMemoryAllocate */
  } sImp;
} tz_shared_memory_t;


/* [TZS] 5.5.2 */
enum {
  TZ_SUCCESS, /* The operation succeeded. */
  TZ_PENDING, /* The asynchronous operation is still pending. */
  TZ_ERROR_ACCESS_DENIED, /* Access has been denied,
                             or the item cannot be found. */
  TZ_ERROR_BUSY, /* The system is busy. */
  TZ_ERROR_CANCEL, /* The execution was cancelled. */
  TZ_ERROR_COMMUNICATION, /* There is a system communication error. */
  TZ_ERROR_DECODE_NO_DATA, /* The decoder ran out of data. */
  TZ_ERROR_DECODE_TYPE, /* The decoder hit a type error. */
  TZ_ERROR_ENCODE_FORMAT, /* The encoded data is of a bad format.
                             This generally applies to incorrectly specified
                             memory references. */
  TZ_ERROR_ENCODE_MEMORY, /* The encoder ran out of memory. */
  TZ_ERROR_GENERIC, /* An unspecified error has occurred. */
  TZ_ERROR_ILLEGAL_ARGUMENT, /* A bad parameter has been specified. */
  TZ_ERROR_ILLEGAL_STATE, /* A state machine has been violated. */
  TZ_ERROR_MEMORY, /* There is not enough memory to perform the operation. */
  TZ_ERROR_NOT_IMPLEMENTED, /* The functionality is not implemented. */
  TZ_ERROR_SECURITY, /* There is a security error. */
  TZ_ERROR_SERVICE, /* The service has returned an error in the service
                       return code variable. */
  TZ_ERROR_SHORT_BUFFER, /* The input buffer is not long enough. */
  TZ_ERROR_UNDEFINED, /* The implementation has reached an
                         UNDEFINED condition. */
};

/* [TZS] 5.5.3 */
enum {
  TZ_STATE_UNDEFINED=0, /* Structures in the UNDEFINED state may have
                           any value for their state constant; it may
                           not exist as an explicit value.  Clients
                           should never make use of this constant,
                           although an implementation may use it
                           internally for debugging purposes. */
  TZ_STATE_INVALID, /* The state is in a safe invalid state. */
  TZ_STATE_OPEN, /* The state is open. */
  TZ_STATE_CLOSING, /* The state is closing, but not yet closed. */
  TZ_STATE_ENCODE, /* The state an operation that is not running and
                      can accept data to be encoded. */
  TZ_STATE_PERFORMABLE, /* The state of an operation that is not
                           running, but which cannot accept data to be
                           encoded. This state applies only to close
                           operations. */
  TZ_STATE_RUNNING, /* The state of an operation that is executing
                       synchronously. */
  TZ_STATE_RUNNING_ASYNC, /* The state of an operation that is
                             executing asynchronously. */
  TZ_STATE_DECODE, /* The state of an operation that can have data
                      read using the decoder functions. */
};

/* [TZS] 5.5.4 */
/* FIXME: should these be an enum? or literal tz_property_t's, or...? */
#if 0
TZ_PROPERTY_SVC_UUID /* The UUID of the service, provided as an array
                        uint8_t values of length 16. The array is not
                        zero-terminated. */
TZ_PROPERTY_SVC_NAME /* The human-readable name of the service,
                        provided as an array of uint8_t values of
                        variable length. The array is
                        zero-terminated. */
TZ_PROPERTY_SVC_VENDOR /* The human-readable name of the service
                          vendor, provided as an array of uint8_t
                          values of variable length. The array is
                          zero- terminated. */
#endif

/* [TZS] 5.5.4.1 Property namespaces */
enum {
  TZ_NAMESPACE_SYSTEM, /* This namespace is used for all system
                          properties returned by the TZSystem
                          functions. */
  TZ_NAMESPACE_SERVICE, /* This namespace is used for general service
                           properties. */
  TZ_NAMESPACE_CLIENT, /* This namespace is reserved for client
                          properties and should not need to be used by
                          a client using this API. */
  TZ_NAMESPACE_CONFIG, /* This namespace is reserved for private
                          configuration properties which are not
                          exposed to the client. */
};

/* [TZS] 5.5.5 System properties */
#if 0
/* TZ_PROPERTY_SYS_API_VERSION The version number of the API. This property’s value is a */
/* single uint32_t. The top 16 bits of the value are the */
/* major version, the bottom 16 bits are minor version. */
/* The value for this version of the specification will be */
/* 0x00030000. */
/* TZ_PROPERTY_SYS_MEMORY_ALIGN The shared memory alignment constraints on memory */
/* references required for efficient memory coherency with */
/* hardware devices. This property’s value is a single */
/* uint32_t. */
/* Value is implementation-defined. */
#endif

/* 5.5.6 Login flags */
#if 0
/* TZ_LOGIN_PUBLIC No login is to be used. */
/* TZ_LOGIN_CLIENT_DATA A buffer of client data is to be provided. */
/* TZ_LOGIN_USER The user executing the application is provided. */
/* TZ_LOGIN_GROUP The user group executing the application is provided. */
/*   TZ_LOGIN_NAME The name of the application is provided; may include path */
/*              information. */
/* TZ_LOGIN_DIGEST The digest of the client application is provided. */
/* TZ_LOGIN_ALL A utility constant indicating all available login types should be used. */
#endif

#define TZ_MEM_SERVICE_RO (1<<0) /* Service can only read from the memory block. */
#define TZ_MEM_SERVICE_WO (1<<1) /* Service can only write from the memory block. */
#define TZ_MEM_SERVICE_RW (TZ_MEM_SERVICE_RO | TZ_MEM_SERVICE_WO) /* Service can read and write from the memory block. */

/* 5.5.8 Decode data types */
enum {
  TZ_TYPE_NONE, /* There is no more data in the decode stream. */
  TZ_TYPE_UINT32, /* The next data type in the stream is a uint32_t. */
  TZ_TYPE_ARRAY, /* The next data type in the stream is an array. */
};

/* no-op macros for documentation */
#define IN
#define OUT
#define INOUT

/* used by device back-ends to register themselves */
tz_return_t TZIDeviceRegister(const char *name, tzi_device_cb_block_t* cbb);

/* 6.1.1 TZDeviceOpen */
tz_return_t
TZDeviceOpen(IN void const *pkDeviceName,
             IN void const *pkInit,
             OUT tz_device_t *psDevice);

/* 6.1.2 TZDeviceClose */
tz_return_t
TZDeviceClose(INOUT tz_device_t *psDevice);

/* 6.1.3 TZDeviceGetTimeLimit */
tz_return_t
TZDeviceGetTimeLimit(INOUT tz_device_t * psDevice,
                     uint32_t uiTimeout,
                     OUT tz_timelimit_t * psTimeLimit);

/* 6.1.4 TZOperationPrepareOpen */
tz_return_t
TZOperationPrepareOpen(INOUT tz_device_t* psDevice,
                       IN tz_uuid_t const * pksService,
                       IN tz_login_t const * pksLogin,
                       IN tz_timelimit_t const * pksTimeLimit,
                       OUT tz_session_t* psSession,
                       OUT tz_operation_t* psOperation);

/* 6.1.5 TZOperationPrepareInvoke */
tz_return_t
TZOperationPrepareInvoke(INOUT tz_session_t* psSession,
                         uint32_t uiCommand,
                         IN tz_timelimit_t const * pksTimeLimit,
                         OUT tz_operation_t * psOperation);

/* 6.1.6 TZOperationPrepareClose */
tz_return_t
TZOperationPrepareClose(INOUT tz_session_t* psSession,
                        OUT tz_operation_t* psOperation);

/* 6.1.7 TZOperationPerform */
tz_return_t
TZOperationPerform(INOUT tz_operation_t* psOperation,
                   OUT tz_return_t* puiServiceReturn);

/* 6.1.8 TZOperationRelease */
void
TZOperationRelease(INOUT tz_operation_t* psOperation);

/* 6.1.9 TZOperationCancel */
void
TZOperationCancel(INOUT tz_operation_t* psOperation);

/* 6.1.10 TZSharedMemoryAllocate */
tz_return_t
TZSharedMemoryAllocate(INOUT tz_session_t* psSession,
                       INOUT tz_shared_memory_t* psSharedMem);

/* 6.1.11 TZSharedMemoryRegister */
tz_return_t
TZSharedMemoryRegister(INOUT tz_session_t* psSession,
                       INOUT tz_shared_memory_t* psSharedMem);

/* 6.1.12 TZSharedMemoryRelease */
void
TZSharedMemoryRelease(INOUT tz_shared_memory_t* psSharedMem);

/* 6.1.13 TZSystemGetPropertyList */
tz_return_t
TZSystemGetPropertyList(INOUT tz_device_t* psDevice,
                        OUT tz_property_name_t* psList,
                        OUT uint32_t* puiLength);

/* 6.1.14 TZSystemGetProperty */
tz_return_t
TZSystemGetProperty(INOUT tz_device_t* psDevice,
                    INOUT tz_property_t* psProperty);

/* 6.2.1 TZEncodeUint32 */
void
TZEncodeUint32(INOUT tz_operation_t* psOperation,
               uint32_t uiData);

/* 6.2.2 TZEncodeArray */
void TZEncodeArray(INOUT tz_operation_t* psOperation,
                   IN void const * pkArray,
                   uint32_t uiLength);

/* 6.2.3 TZEncodeArraySpace */
void * TZEncodeArraySpace(INOUT tz_operation_t* psOperation,
                          uint32_t uiLength);

/* 6.2.4 TZEncodeMemoryReference */
void
TZEncodeMemoryReference(INOUT tz_operation_t* psOperation,
                        INOUT tz_shared_memory_t* psSharedMem,
                        uint32_t uiOffset,
                        uint32_t uiLength,
                        uint32_t uiFlags);

/* extension: encode multiple by format string */

/*                                  expects        see                 */
#define TZI_EU32 PRIu32          /* (u32)          TZEncodeUint32     */
#define TZI_ESTR "s"             /* (char*)        TZEncodeArray      */
/*                                  encodes as an array, up to and
                                         including null terminator     */
#define TZI_EARR "p%"PRIu32      /* (void*, u32)   TZEncodeArray      */
#define TZI_EARRSPC "-p%"PRIu32  /* (void**, u32)  TZEncodeArraySpace */

/* Convenience functions for encoding multiple parameters. Use the
 * format-specifier macros TZI_E*
 */
tz_return_t
TZIEncodeF(INOUT tz_operation_t *psOperation, const char* str, ...)
  __attribute__ ((format (printf, 2, 3)));

tz_return_t
vTZIEncodeF(INOUT tz_operation_t *psOperation, const char* str, va_list argp);

/*                                       expects        see                 */
#define TZI_DU32 PRIu32               /* (u32*)         TZDecodeUint32     */
#define TZI_DARRSPC "p%"PRIu32        /* (void**, u32*) TZDecodeArraySpace */
#define TZI_DARRSPC_NOLEN "p%*"PRIu32 /* (void**)       TZDecodeArraySpace */
#define TZI_DARR "s%"PRIu32           /* (void*, u32*)  TZDecodeArraySpace */
/*                                       checks second parameter for
                                         buffer size, copies into
                                         buffer spec'd by first
                                         parameter, and sets second
                                         parameter to size of decoded
                                         buffer */
#define TZI_DARR_NOLEN "s%*"PRIu32    /* (void*)        TZI_DARR */

/* Convenience functions for decoding multiple paramters. Use the
 * format-specifier macros TZI_D*
 */
tz_return_t
TZIDecodeF(INOUT tz_operation_t *psOperation, const char* str, ...)
  __attribute__ ((format (scanf, 2, 3)));

tz_return_t
vTZIDecodeF(INOUT tz_operation_t *psOperation, const char* str, va_list argp);

/* 6.2.5 TZDecodeUint32 */
uint32_t
TZDecodeUint32(INOUT tz_operation_t* psOperation);


/* 6.2.6 TZDecodeArraySpace */
void *
TZDecodeArraySpace(INOUT tz_operation_t* psOperation,
                   OUT uint32_t* puiLength);


/* 6.2.7 TZDecodeGetType */
uint32_t
TZDecodeGetType(INOUT tz_operation_t* psOperation);

/* 6.2.8 TZDecodeGetError */
tz_return_t
TZDecodeGetError(INOUT tz_operation_t * psOperation);

/* 6.3.1 TZManagerOpen */
tz_return_t
TZManagerOpen(INOUT tz_device_t* psDevice,
              IN tz_login_t const * pksLogin,
              OUT tz_session_t* psSession);

/* 6.3.2 TZManagerClose */
tz_return_t
TZManagerClose(INOUT tz_session_t* psSession);

/* 6.3.3 TZManagerGetServiceList */
tz_return_t
TZManagerGetServiceList(INOUT tz_session_t* psSession,
                        OUT tz_uuid_t* psList,
                        INOUT uint32_t* puiLength);

/* 6.3.4 TZManagerGetServicePropertyList */
tz_return_t
TZManagerGetServicePropertyList(INOUT tz_session_t* psSession,
                                IN tz_uuid_t const * pksService,
                                OUT tz_property_name_t * pasList,
                                INOUT uint32_t * puiLength);

/* 6.3.5 TZManagerGetServiceProperty */
tz_return_t
TZManagerGetServiceProperty(INOUT tz_session_t* psSession,
                            IN tz_uuid_t const* pksService,
                            INOUT tz_property_t* psProperty);

/* 7.2.1 TZManagerDownloadService */
/* note- kauiData is uint8_t* by standard. making it void*
 * so that caller doesn't need to explicitly cast.
 */
tz_return_t
TZManagerDownloadService(INOUT tz_session_t* psSession,
                         IN void const * kauiData, 
                         uint32_t uiLength,
                         OUT tz_uuid_t* psService);

/* 7.2.2 TZManagerRemoveService */
tz_return_t
TZManagerRemoveService(INOUT tz_session_t* psSession,
                       IN tz_uuid_t const * pksService);

/******************************************************/
/* implementation-specific. using prefix 'tv' for now */
/******************************************************/

/* typedef struct etz_service_handle_t { */
/*   tz_uuid_t sId; */
/*   uint32_t activeSessions; */
/*   tz_return_t (*pCall)(struct etz_service_handle_t*, tz_session_t*); */
/*   tz_return_t (*pRemove)(struct etz_service_handle_t*); */
/* } etz_service_handle_t; */

/* /\* service descriptor to be passed to */
/*  * TZManagerDownloadService. Think */
/*  * of this is an 'abstract interface'. */
/*  * Specific service descriptor types will */
/*  * include this as their first struct element. */
/*  *\/ */
/* typedef struct etz_service_t { */
/*   tz_uuid_t sId; */
/*   tz_return_t (*pDownload)(const struct etz_service_t*, etz_service_handle_t**); */
/* } etz_service_t; */


/**********************************************************/

#endif
