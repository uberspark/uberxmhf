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

// FIFO queue implementation using Windows Kernel-mode
// DL Lists
// author: amit vasudevan (amitvasudevan@acm.org)

#include <ndis.h>
#include <ntdef.h>

#include "txrxfifo.h"

PTXRXFIFOENTRY pTxfifohead=NULL;
PTXRXFIFOENTRY pRxfifohead=NULL;
KSPIN_LOCK	txfifoLock;
KSPIN_LOCK	rxfifoLock;

//---initializes the TX and RX FIFO queues--------------------------------------
NTSTATUS txrxfifo_initialize(void){
	pTxfifohead = (PTXRXFIFOENTRY) ExAllocatePoolWithTag( NonPagedPool, 
					sizeof(TXRXFIFOENTRY), LDNVNET_POOLTAG_TXFIFO );
	
	
	pRxfifohead = (PTXRXFIFOENTRY) ExAllocatePoolWithTag( NonPagedPool, 
					sizeof(TXRXFIFOENTRY), LDNVNET_POOLTAG_RXFIFO );


	if( !pTxfifohead || !pRxfifohead )
		return STATUS_INSUFFICIENT_RESOURCES;
	
	DEBUGP(MP_ERROR, ("%s: pTxfifohead=0x%08x, pRxfifohead=0x%08x\n",
		__FUNCTION__, pTxfifohead, pRxfifohead));

	//initialize spin locks associated with the above
	KeInitializeSpinLock(&txfifoLock);
	KeInitializeSpinLock(&rxfifoLock);

	//initialize list heads for Tx and Rx
	InitializeListHead(&pTxfifohead->ListEntry);
	InitializeListHead(&pRxfifohead->ListEntry);


	return STATUS_SUCCESS;
}

//---free the TX and RX FIFO queue heads----------------------------------------
NTSTATUS txrxfifo_free(void){
 	ExFreePoolWithTag(pTxfifohead, LDNVNET_POOLTAG_TXFIFO);
 	ExFreePoolWithTag(pRxfifohead, LDNVNET_POOLTAG_RXFIFO);
}


//---put an entry into the TX FIFO----------------------------------------------
NTSTATUS txrxfifo_txfifo_add(UCHAR *payload, ULONG length){
	PTXRXFIFOENTRY pTxEntry;
	
	ASSERT(payload != NULL && length <= ETH_MAX_PACKET_SIZE );
	
	//allocate memory for a Tx FIFO entry
	pTxEntry = (PTXRXFIFOENTRY) ExAllocatePoolWithTag( NonPagedPool, 
					sizeof(TXRXFIFOENTRY), LDNVNET_POOLTAG_TXFIFO );
					
	if(!pTxEntry){
		DEBUGP(MP_ERROR, ("%s: could not allocate entry in Tx FIFO\n",
		__FUNCTION__));
		return STATUS_INSUFFICIENT_RESOURCES;
	}
	
	
	//copy the payload into the Tx FIFO entry and set correct length
	memcpy(pTxEntry->payload, payload, length);
	pTxEntry->payloadLength = length;
	
	//insert this entry into the Tx FIFO queue
	ExInterlockedInsertTailList(&pTxfifohead->ListEntry, &pTxEntry->ListEntry,
		&txfifoLock);

	return STATUS_SUCCESS;
}


//---remove an entry from the TX FIFO----------------------------------------------
NTSTATUS txrxfifo_txfifo_remove(UCHAR *buffer, ULONG *length){
	PTXRXFIFOENTRY pTxEntry;
	
	ASSERT(buffer != NULL && length != NULL);
		
	pTxEntry = (PTXRXFIFOENTRY) ExInterlockedRemoveHeadList(&pTxfifohead->ListEntry, 
																&txfifoLock);
																
	if(pTxEntry == NULL)
		return STATUS_NO_MORE_ENTRIES;
		
	
	memcpy(buffer, pTxEntry->payload, pTxEntry->payloadLength);
	*length = pTxEntry->payloadLength;
	
	ExFreePoolWithTag(pTxEntry, LDNVNET_POOLTAG_TXFIFO);		
	
	return STATUS_SUCCESS;
}


//---put an entry into the RX FIFO----------------------------------------------
NTSTATUS txrxfifo_rxfifo_add(UCHAR *payload, ULONG length){
	PTXRXFIFOENTRY pRxEntry;
	
	ASSERT(payload != NULL && length <= ETH_MAX_PACKET_SIZE );
	
	//allocate memory for a Tx FIFO entry
	pRxEntry = (PTXRXFIFOENTRY) ExAllocatePoolWithTag( NonPagedPool, 
					sizeof(TXRXFIFOENTRY), LDNVNET_POOLTAG_RXFIFO );
					
	if(!pRxEntry){
		DEBUGP(MP_ERROR, ("%s: could not allocate entry in Rx FIFO\n",
		__FUNCTION__));
		return STATUS_INSUFFICIENT_RESOURCES;
	}
	
	
	//copy the payload into the Rx FIFO entry and set correct length
	memcpy(pRxEntry->payload, payload, length);
	pRxEntry->payloadLength = length;
	
	//insert this entry into the Rx FIFO queue
	ExInterlockedInsertTailList(&pRxfifohead->ListEntry, &pRxEntry->ListEntry,
		&rxfifoLock);

	return STATUS_SUCCESS;
}

//---remove an entry from the RX FIFO----------------------------------------------
NTSTATUS txrxfifo_rxfifo_remove(UCHAR *buffer, ULONG *length){
	PTXRXFIFOENTRY pRxEntry;
	
	ASSERT(buffer != NULL && length != NULL);
		
	pRxEntry = (PTXRXFIFOENTRY) ExInterlockedRemoveHeadList(&pRxfifohead->ListEntry, 
																&rxfifoLock);
																
	if(pRxEntry == NULL)
		return STATUS_NO_MORE_ENTRIES;
		
	
	memcpy(buffer, pRxEntry->payload, pRxEntry->payloadLength);
	*length = pRxEntry->payloadLength;
	
	ExFreePoolWithTag(pRxEntry, LDNVNET_POOLTAG_RXFIFO);		
	
	return STATUS_SUCCESS;
}
