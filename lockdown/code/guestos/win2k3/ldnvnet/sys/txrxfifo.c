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