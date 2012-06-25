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

/*++

Copyright (c) Microsoft Corporation.  All rights reserved.

    THIS CODE AND INFORMATION IS PROVIDED "AS IS" WITHOUT WARRANTY OF ANY
    KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE
    IMPLIED WARRANTIES OF MERCHANTABILITY AND/OR FITNESS FOR A PARTICULAR
    PURPOSE.

Module Name:

   IOCTL.C

Abstract:

    This modules contains functions to register/deregsiter a control-
    deviceobject for ioctl purposes and dispatch routine for handling
    ioctl requests from usermode.

Revision History:

Notes:

--*/

#if defined(IOCTL_INTERFACE)


#include "miniport.h"
#include "public.h"
#include "txrxfifo.h"

//
// Simple Mutual Exclusion constructs used in preference to
// using KeXXX calls since we don't have Mutex calls in NDIS.
// These can only be called at passive IRQL.
//

typedef struct _NIC_MUTEX
{
    ULONG                   Counter;
    ULONG                   ModuleAndLine;  // useful for debugging

} NIC_MUTEX, *PNIC_MUTEX;

#define NIC_INIT_MUTEX(_pMutex)                                 \
{                                                               \
    (_pMutex)->Counter = 0;                                     \
    (_pMutex)->ModuleAndLine = 0;                               \
}

#define NIC_ACQUIRE_MUTEX(_pMutex)                              \
{                                                               \
    while (NdisInterlockedIncrement((PLONG)&((_pMutex)->Counter)) != 1)\
    {                                                           \
        NdisInterlockedDecrement((PLONG)&((_pMutex)->Counter));        \
        NdisMSleep(10000);                                      \
    }                                                           \
    (_pMutex)->ModuleAndLine = ('I' << 16) | __LINE__;\
}

#define NIC_RELEASE_MUTEX(_pMutex)                              \
{                                                               \
    (_pMutex)->ModuleAndLine = 0;                               \
    NdisInterlockedDecrement((PLONG)&(_pMutex)->Counter);              \
}

#define LINKNAME_STRING     L"\\DosDevices\\LDNVNET"
#define NTDEVICE_STRING     L"\\Device\\LDNVNET"

//
// Global variables
//

NDIS_HANDLE        NdisDeviceHandle = NULL; // From NdisMRegisterDevice
LONG               MiniportCount = 0; // Total number of miniports in existance
PDEVICE_OBJECT     ControlDeviceObject = NULL;  // Device for IOCTLs
NIC_MUTEX          ControlDeviceMutex;
extern NDIS_HANDLE NdisWrapperHandle;

#pragma NDIS_PAGEABLE_FUNCTION(NICRegisterDevice)
#pragma NDIS_PAGEABLE_FUNCTION(NICDeregisterDevice)
#pragma NDIS_PAGEABLE_FUNCTION(NICDispatch)


NDIS_STATUS
NICRegisterDevice(
    VOID
    )
/*++

Routine Description:

    Register an ioctl interface - a device object to be used for this
    purpose is created by NDIS when we call NdisMRegisterDevice.

    This routine is called whenever a new miniport instance is
    initialized. However, we only create one global device object,
    when the first miniport instance is initialized. This routine
    handles potential race conditions with NICDeregisterDevice via
    the ControlDeviceMutex.

    NOTE: do not call this from DriverEntry; it will prevent the driver
    from being unloaded (e.g. on uninstall).

Arguments:

    None

Return Value:

    NDIS_STATUS_SUCCESS if we successfully register a device object.

--*/
{
    NDIS_STATUS         Status = NDIS_STATUS_SUCCESS;
    UNICODE_STRING      DeviceName;
    UNICODE_STRING      DeviceLinkUnicodeString;
    PDRIVER_DISPATCH    DispatchTable[IRP_MJ_MAXIMUM_FUNCTION+1];

    DEBUGP(MP_TRACE, ("==>NICRegisterDevice\n"));

    PAGED_CODE();

    NIC_ACQUIRE_MUTEX(&ControlDeviceMutex);

    ++MiniportCount;
    
    if (1 == MiniportCount)
    {
        NdisZeroMemory(DispatchTable, (IRP_MJ_MAXIMUM_FUNCTION+1) * sizeof(PDRIVER_DISPATCH));
        
        DispatchTable[IRP_MJ_CREATE] = NICDispatch;
        DispatchTable[IRP_MJ_CLEANUP] = NICDispatch;
        DispatchTable[IRP_MJ_CLOSE] = NICDispatch;
        DispatchTable[IRP_MJ_DEVICE_CONTROL] = NICDispatch;
        

        NdisInitUnicodeString(&DeviceName, NTDEVICE_STRING);
        NdisInitUnicodeString(&DeviceLinkUnicodeString, LINKNAME_STRING);

        //
        // Create a device object and register our dispatch handlers
        //
        Status = NdisMRegisterDevice(
                    NdisWrapperHandle, 
                    &DeviceName,
                    &DeviceLinkUnicodeString,
                    &DispatchTable[0],
                    &ControlDeviceObject,
                    &NdisDeviceHandle
                    );
    }

    NIC_RELEASE_MUTEX(&ControlDeviceMutex);

    DEBUGP(MP_TRACE, ("<==NICRegisterDevice: %x\n", Status));

    return (Status);
}


NTSTATUS
NICDispatch(
    IN PDEVICE_OBJECT           DeviceObject,
    IN PIRP                     Irp
    )
/*++
Routine Description:

    Process IRPs sent to this device.

Arguments:

    DeviceObject - pointer to a device object
    Irp      - pointer to an I/O Request Packet

Return Value:

    NTSTATUS - STATUS_SUCCESS always - change this when adding
    real code to handle ioctls.

--*/
{
    PIO_STACK_LOCATION  irpStack;
    NTSTATUS            status = STATUS_SUCCESS;
    ULONG               inlen;
    PVOID               buffer;

    PAGED_CODE();
    
    irpStack = IoGetCurrentIrpStackLocation(Irp);
    DEBUGP(MP_TRACE, ("==>NICDispatch %d\n", irpStack->MajorFunction));
      
    switch (irpStack->MajorFunction)
    {
        case IRP_MJ_CREATE:
    Irp->IoStatus.Information = 0;
 
            break;
        
        case IRP_MJ_CLEANUP:
    Irp->IoStatus.Information = 0;
 
            break;
        
        case IRP_MJ_CLOSE:
    Irp->IoStatus.Information = 0;
 
            break;        
        
        case IRP_MJ_DEVICE_CONTROL: 
        {

          buffer = Irp->AssociatedIrp.SystemBuffer;  
          inlen = irpStack->Parameters.DeviceIoControl.InputBufferLength;
          
          switch (irpStack->Parameters.DeviceIoControl.IoControlCode) 
          {

            //
            // Add code here to handle ioctl commands.
            //
            case IOCTL_LDNVNET_READ_DATA:{
						    	PCHAR buffer;
						    	ULONG length;
						    	NTSTATUS opStatus  = STATUS_SUCCESS;

									buffer = Irp->AssociatedIrp.SystemBuffer;
								 	opStatus = txrxfifo_txfifo_remove(buffer, &length);
									if(opStatus == STATUS_SUCCESS)
										Irp->IoStatus.Information = length;
									else
										Irp->IoStatus.Information = 0;
									
									if(Irp->IoStatus.Information)
										DEBUGP(MP_ERROR, ("IOCTL(READ): returned %u bytes\n", 
														Irp->IoStatus.Information));
								}
                break;
            case IOCTL_LDNVNET_WRITE_DATA:{
                PCHAR buffer;
                ULONG length;
                NTSTATUS opStatus = STATUS_SUCCESS;
                buffer = Irp->AssociatedIrp.SystemBuffer;
                length = irpStack->Parameters.DeviceIoControl.InputBufferLength;
                
                opStatus = txrxfifo_rxfifo_add(buffer, length);
								if(opStatus == STATUS_SUCCESS)
									Irp->IoStatus.Information = length;
								else
									Irp->IoStatus.Information = 0;
								
                
                	if(Irp->IoStatus.Information)
										DEBUGP(MP_ERROR, ("IOCTL(WRITE): returned %u bytes\n", 
														Irp->IoStatus.Information));
 								}
                break;
            default:
 						    Irp->IoStatus.Information = 0;
 						    status = STATUS_UNSUCCESSFUL;
                break;
          }
          break;  
        }
        default:
            break;
    }
 
    Irp->IoStatus.Status = status;
    IoCompleteRequest(Irp, IO_NO_INCREMENT);

    DEBUGP(MP_TRACE, ("<== NIC Dispatch\n"));

    return status;

} 


NDIS_STATUS
NICDeregisterDevice(
    VOID
    )
/*++

Routine Description:

    Deregister the ioctl interface. This is called whenever a miniport
    instance is halted. When the last miniport instance is halted, we
    request NDIS to delete the device object

Arguments:

    NdisDeviceHandle - Handle returned by NdisMRegisterDevice

Return Value:

    NDIS_STATUS_SUCCESS if everything worked ok

--*/
{
    NDIS_STATUS Status = NDIS_STATUS_SUCCESS;

    DEBUGP(MP_TRACE, ("==>NICDeregisterDevice\n"));

    PAGED_CODE();

    NIC_ACQUIRE_MUTEX(&ControlDeviceMutex);

    ASSERT(MiniportCount > 0);

    --MiniportCount;
    
    if (0 == MiniportCount)
    {
        //
        // All miniport instances have been halted.
        // Deregister the control device.
        //

        if (NdisDeviceHandle != NULL)
        {
            Status = NdisMDeregisterDevice(NdisDeviceHandle);
            NdisDeviceHandle = NULL;
        }
    }

    NIC_RELEASE_MUTEX(&ControlDeviceMutex);

    DEBUGP(MP_TRACE, ("<== NICDeregisterDevice: %x\n", Status));
    return Status;
    
}

#endif



