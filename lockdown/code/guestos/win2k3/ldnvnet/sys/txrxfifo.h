// Tx/Rx FIFO declarations and constants
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef _TXRXFIFO_H
#define _TXRXFIFO_H

#include "miniport.h"

#define LDNVNET_POOLTAG_TXFIFO		'TndL'
#define LDNVNET_POOLTAG_RXFIFO		'RndL'

typedef struct _txrxfifoentry {
	LIST_ENTRY	ListEntry;	//list entry to place structure on DL List
	UCHAR payload[ETH_MAX_PACKET_SIZE];
	ULONG payloadLength;

} TXRXFIFOENTRY, *PTXRXFIFOENTRY;

NTSTATUS txrxfifo_initialize(void);
NTSTATUS txrxfifo_free(void);
NTSTATUS txrxfifo_txfifo_add(UCHAR *payload, ULONG length);
NTSTATUS txrxfifo_txfifo_remove(UCHAR *buffer, ULONG *length);

#endif //_TXRXFIFO_H