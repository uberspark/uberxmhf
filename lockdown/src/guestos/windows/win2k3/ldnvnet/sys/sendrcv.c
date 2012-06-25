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

        SendRCV.C
        
Abstract:

    This module contains miniport functions for handling Send & Receive
    packets and other helper routines called by these miniport functions.

    In order to excercise the send and receive code path of this driver, 
    you should install more than one instance of the miniport. If there 
    is only one instance installed, the driver throws the send packet on
    the floor and completes the send successfully. If there are more 
    instances present, it indicates the incoming send packet to the other
    instances. For example, if there 3 instances: A, B, & C installed. 
    Packets coming in for A instance would be indicated to B & C; packets 
    coming into B would be indicated to C, & A; and packets coming to C 
    would be indicated to A & B. 
    
Revision History:

Notes:

--*/
#include "miniport.h"
#include "txrxfifo.h"

//returns TRUE on success, FALSE on error
BOOLEAN	GetPacketBufferData(PMP_ADAPTER Adapter,
    PNDIS_PACKET Packet,
		PUCHAR	buffer, 
		PULONG	length){
    INT               Equal;            
    UINT              PacketLength;
    PNDIS_BUFFER      FirstBuffer = NULL;
    PUCHAR            Address = NULL;
    UINT              CurrentLength;
	  ULONG             index;
    BOOLEAN           result = FALSE;
  	ULONG							bufferOffset=0;  
    PNDIS_BUFFER      CurrentBuffer = NULL;
    PNDIS_BUFFER      NextBuffer = NULL;

#ifdef NDIS51_MINIPORT
       NdisGetFirstBufferFromPacketSafe(
            Packet,
            &FirstBuffer,
            &Address,
            &CurrentLength,
            &PacketLength,
            NormalPagePriority);
#else
       NdisGetFirstBufferFromPacket(
            Packet,
            &FirstBuffer,
            &Address,
            &CurrentLength,
            &PacketLength);
#endif

	if(PacketLength == 0 || PacketLength > NIC_BUFFER_SIZE)
		return FALSE;

	//if the entire packet is in this buffer, then copy and return	
	if(CurrentLength == PacketLength){
		*length=PacketLength;
		memcpy(buffer, 	Address, PacketLength);
		return TRUE;
	}

	//there are more buffers following, first copy this one
	memcpy(buffer, Address, CurrentLength);
	bufferOffset+=CurrentLength;
	CurrentBuffer = FirstBuffer;
	
	while(1){
		//get next buffer
		NdisGetNextBuffer(CurrentBuffer, &NextBuffer);
		
		if(NextBuffer == NULL){
			break;
		}

		CurrentBuffer=NextBuffer;
		
		//query the buffer
		NdisQueryBuffer(CurrentBuffer, &Address, &CurrentLength);
		
		//copy this buffer contents
		memcpy((buffer+bufferOffset), Address, CurrentLength);
		bufferOffset+=CurrentLength;
	}

	*length=PacketLength;
	return TRUE;	
}
/*

PUCHAR	GetPacketBufferData(    PMP_ADAPTER Adapter,
    PNDIS_PACKET Packet, 
		PULONG	length){
    INT               Equal;            
    UINT              PacketLength;
    PNDIS_BUFFER      FirstBuffer = NULL;
    PUCHAR            Address = NULL;
    UINT              CurrentLength;
    ULONG             index;
    BOOLEAN           result = FALSE;
    
   
#ifdef NDIS51_MINIPORT
       NdisGetFirstBufferFromPacketSafe(
            Packet,
            &FirstBuffer,
            &Address,
            &CurrentLength,
            &PacketLength,
            NormalPagePriority);
#else
       NdisGetFirstBufferFromPacket(
            Packet,
            &FirstBuffer,
            &Address,
            &CurrentLength,
            &PacketLength);
#endif
        
        if(PacketLength != CurrentLength)
        	
        DEBUGP(MP_LOUD, ("BLASTED!!! Packetlength=%u, CurrentLength=%u\n",
						PacketLength, CurrentLength));

        *length=(ULONG)PacketLength;
				return (Address);
		
}
*/

VOID 
MPSendPackets(
    IN  NDIS_HANDLE             MiniportAdapterContext,
    IN  PPNDIS_PACKET           PacketArray,
    IN  UINT                    NumberOfPackets)
/*++

Routine Description:

    Send Packet Array handler. Called by NDIS whenever a protocol
    bound to our miniport sends one or more packets.

    The input packet descriptor pointers have been ordered according 
    to the order in which the packets should be sent over the network 
    by the protocol driver that set up the packet array. The NDIS 
    library preserves the protocol-determined ordering when it submits
    each packet array to MiniportSendPackets

    As a deserialized driver, we are responsible for holding incoming send 
    packets in our internal queue until they can be transmitted over the 
    network and for preserving the protocol-determined ordering of packet
    descriptors incoming to its MiniportSendPackets function. 
    A deserialized miniport driver must complete each incoming send packet
    with NdisMSendComplete, and it cannot call NdisMSendResourcesAvailable. 

    Runs at IRQL <= DISPATCH_LEVEL
    
Arguments:

    MiniportAdapterContext    Pointer to our adapter context
    PacketArray               Set of packets to send
    NumberOfPackets           Length of above array

Return Value:

    None
    
--*/
{
    PMP_ADAPTER       Adapter;
    NDIS_STATUS       Status;
    UINT              PacketCount;

    DEBUGP(MP_TRACE, ("---> MPSendPackets\n"));

    Adapter = (PMP_ADAPTER)MiniportAdapterContext;

    for(PacketCount=0;PacketCount < NumberOfPackets; PacketCount++)
    {
        //
        // Check for a zero pointer
        //
        ASSERT(PacketArray[PacketCount]);

        Status = NICSendPacket(Adapter, PacketArray[PacketCount]);

    }

    DEBUGP(MP_TRACE, ("<--- MPSendPackets\n"));

    return;
}

VOID 
MPReturnPacket(
    IN NDIS_HANDLE  MiniportAdapterContext,
    IN PNDIS_PACKET Packet)
/*++

Routine Description:

    NDIS Miniport entry point called whenever protocols are done with
    a packet that we had indicated up and they had queued up for returning
    later.

Arguments:

    MiniportAdapterContext    - pointer to MP_ADAPTER structure
    Packet    - packet being returned.

Return Value:

    None.

--*/
{
    PMP_ADAPTER Adapter = (PMP_ADAPTER) MiniportAdapterContext;

    DEBUGP(MP_TRACE, ("---> MPReturnPacket\n"));

    //NICFreeRecvPacket(Adapter, Packet);
    
    DEBUGP(MP_TRACE, ("<--- MPReturnPacket\n"));
}


//--- this routine is called by the OS to transmit a packet OUT-----------------
NDIS_STATUS 
NICSendPacket(
    PMP_ADAPTER Adapter,
    PNDIS_PACKET Packet)
/*++

Routine Description:

    This routine copies the packet content to a TCB, gets a receive packet,
    associates the TCB buffer to this recive packet and queues
    receive packet with the same data on one or more miniport instances
    controlled by this driver. For receive path to be active, you have
    to install more than one instance of this miniport.
        
Arguments:

    Adapter    - pointer to the MP_ADAPTER structure
    Packet    - packet to be transfered.


Return Value:

    NDIS_STATUS_SUCCESS or NDIS_STATUS_PENDING

--*/
{
    PMP_ADAPTER       DestAdapter;
    NDIS_STATUS       Status = NDIS_STATUS_SUCCESS;
    PTCB              pTCB = NULL;
		PUCHAR						BufferAddr=NULL;
		ULONG							p_BufferAddr;
		ULONG							p_Length, i;
		PUCHAR						p;
		NTSTATUS					opStatus;
		
    DEBUGP(MP_TRACE, ("--> NICSendPacket, Packet= %p\n", Packet));


		//
		//if(MP_IS_READY(Adapter) && 
		//		NICIsPacketTransmittable(Adapter, Packet)){
		if(MP_IS_READY(Adapter)){
			if(GetPacketBufferData(Adapter, Packet, &Adapter->LdnSendPacketBufferData[0], &p_Length)){
				p_BufferAddr = (ULONG)&Adapter->LdnSendPacketBufferData[0];
			
			  DEBUGP(MP_ERROR, ("OUT: size=%u bytes\n", p_Length));
				opStatus = txrxfifo_txfifo_add(p_BufferAddr, p_Length);
				if(opStatus != STATUS_SUCCESS){
					DEBUGP(MP_ERROR, ("%s: Tx FIFO full, rejecting...\n", __FUNCTION__));
				}		
			
			/*p=(PUCHAR)p_BufferAddr;	
			
			DEBUGP(MP_INFO, ("Send, Size=%u bytes\n", 
                            p_Length));

      DEBUGP(MP_INFO, ("\nPacket Dump.\n"));
      for(i=0; i < p_Length; i++)
				DEBUGP(MP_INFO, ("0x%02X ", 
                            p[i]));
          
      DEBUGP(MP_INFO, ("\nDone.\n"));*/
                              
	    /*
			//send it out to our VMM				
			#define	__LDN_VMMCALL_PKTSEND		0xC0
    
    	//vmmcall here
			__asm {
				push eax
				push ebx
				push ecx
				
				mov ebx, p_BufferAddr 	
				mov ecx, p_Length
				mov eax, __LDN_VMMCALL_PKTSEND
				
				__emit 0fh
				__emit 01h
				__emit 0d9h
				
				pop ecx
				pop ebx
				pop eax		
			 }
			 */
      
      }else
				DEBUGP(MP_ERROR, ("Could not grab data for send packet\n"));
					
		}
		
		NDIS_SET_PACKET_STATUS(Packet, Status);

    DEBUGP(MP_LOUD, ("Calling NdisMSendComplete \n"));

    Status = NDIS_STATUS_SUCCESS;

    Adapter->GoodTransmits++;

    NdisMSendComplete(
           Adapter->AdapterHandle,
            Packet,
            Status);

    DEBUGP(MP_TRACE, ("<-- NICSendPacket Status = 0x%08x\n", Status));

    return(Status);

}  


VOID
NICIndicateTimer(
    IN PVOID             SystemSpecific1,
    IN PVOID             FunctionContext,
    IN PVOID             SystemSpecific2,
    IN PVOID             SystemSpecific3)
/*++

Routine Description:

    Timer callback function for Receive Indication. Please note that receive
    timer DPC is not required when you are talking to a real device. In real
    miniports, this DPC is usually provided by NDIS as MPHandleInterrupt
    callback whenever the device interrupts for receive indication.
        
Arguments:

FunctionContext - Pointer to our adapter

Return Value:

    VOID

--*/
{

		/*#define	__LDN_VMMCALL_TIMERFIRE				0xA0
    
    //vmmcall here
		__asm {
				push eax

				mov eax, __LDN_VMMCALL_TIMERFIRE
				
				__emit 0fh
				__emit 01h
				__emit 0d9h
				
				pop eax		
			}*/

}



VOID
NICIndicatePoll(
    IN PVOID             SystemSpecific1,
    IN PVOID             FunctionContext,
    IN PVOID             SystemSpecific2,
    IN PVOID             SystemSpecific3)
/*++

Routine Description:

    Timer callback function for Receive Indication. Please note that receive
    timer DPC is not required when you are talking to a real device. In real
    miniports, this DPC is usually provided by NDIS as MPHandleInterrupt
    callback whenever the device interrupts for receive indication.
        
Arguments:

FunctionContext - Pointer to our adapter

Return Value:

    VOID

--*/
{

/*#define __LDN_VMMCALL_DOPOLL					0xA1
    
    //vmmcall here
		__asm {
				push eax

				mov eax, __LDN_VMMCALL_DOPOLL
				
				__emit 0fh
				__emit 01h
				__emit 0d9h
				
				pop eax		
			}
  */
  
}

VOID
NICIndicatePoll_1(
    IN PVOID             SystemSpecific1,
    IN PVOID             FunctionContext,
    IN PVOID             SystemSpecific2,
    IN PVOID             SystemSpecific3)
/*++

Routine Description:

    Timer callback function for Receive Indication. Please note that receive
    timer DPC is not required when you are talking to a real device. In real
    miniports, this DPC is usually provided by NDIS as MPHandleInterrupt
    callback whenever the device interrupts for receive indication.
        
Arguments:

FunctionContext - Pointer to our adapter

Return Value:

    VOID

--*/
{

/*#define __LDN_VMMCALL_DOPOLL_1					0xA2
    
    //vmmcall here
		__asm {
				push eax

				mov eax, __LDN_VMMCALL_DOPOLL_1
				
				__emit 0fh
				__emit 01h
				__emit 0d9h
				
				pop eax		
			}
  */
}

VOID
NICIndicateReceiveTimerDpc(
    IN PVOID             SystemSpecific1,
    IN PVOID             FunctionContext,
    IN PVOID             SystemSpecific2,
    IN PVOID             SystemSpecific3)
/*++

Routine Description:

    Timer callback function for Receive Indication. Please note that receive
    timer DPC is not required when you are talking to a real device. In real
    miniports, this DPC is usually provided by NDIS as MPHandleInterrupt
    callback whenever the device interrupts for receive indication.
        
Arguments:

FunctionContext - Pointer to our adapter

Return Value:

    VOID

--*/
{
    PMP_ADAPTER Adapter = (PMP_ADAPTER)FunctionContext;
    PRCB pRCB = NULL;
    PLIST_ENTRY pEntry = NULL;
    ULONG isPacketAvailable=0;
    ULONG p_PacketLength=0, p_BufferAddr;
  	PNDIS_PACKET PacketArray[1];
   	NTSTATUS opStatus  = STATUS_SUCCESS;
 
    DEBUGP(MP_TRACE, ("--->NICIndicateReceiveTimerDpc = %p\n", Adapter));

    //
    // Increment the ref count on the adapter to prevent the driver from
    // unloding while the DPC is running. The Halt handler waits for the
    // ref count to drop to zero before returning. 
    //
    MP_INC_REF(Adapter); 

		//the next block runs atomically, we acquire a lock
		//invoke the vmm, determine if there
		//is a packet and if so, indicate the packet up and release the lock
    //NdisAcquireSpinLock(&Adapter->RecvLock);
    p_BufferAddr=(ULONG)&Adapter->LdnRecvPacketBufferData[0];
    
/*		#define	__LDN_VMMCALL_PKTRECV		0xC1
    
    //vmmcall here
		__asm {
				push eax
				push ebx
				push ecx
				
				mov ebx, p_BufferAddr
				mov ecx, 0
				mov eax, __LDN_VMMCALL_PKTRECV
				
				__emit 0fh
				__emit 01h
				__emit 0d9h
				
				mov p_PacketLength, ecx
				pop ecx
				pop ebx
				pop eax		
			}
	*/		
	
		/*Adapter->LdnRecvPacketBufferData[0]=0x00;
		Adapter->LdnRecvPacketBufferData[1]=0x15;
		Adapter->LdnRecvPacketBufferData[2]=0x17;
		Adapter->LdnRecvPacketBufferData[3]=0x1C;
		Adapter->LdnRecvPacketBufferData[4]=0x47;
		Adapter->LdnRecvPacketBufferData[5]=0x71;
		Adapter->LdnRecvPacketBufferData[6]=0x00;
		Adapter->LdnRecvPacketBufferData[7]=0x13;
		Adapter->LdnRecvPacketBufferData[8]=0x72;
		Adapter->LdnRecvPacketBufferData[9]=0xF7;
		Adapter->LdnRecvPacketBufferData[10]=0x0B;
		Adapter->LdnRecvPacketBufferData[11]=0xF1;
		Adapter->LdnRecvPacketBufferData[12]=0xAA;
		Adapter->LdnRecvPacketBufferData[13]=0xBB;*/
		
		
	 	opStatus = txrxfifo_rxfifo_remove(p_BufferAddr, &p_PacketLength);
								
		
		if(opStatus == STATUS_SUCCESS && p_PacketLength){
		    NdisAdjustBufferLength(Adapter->LdnRecvPacketBuffer, p_PacketLength);
		    NdisRecalculatePacketCounts(Adapter->LdnRecvPacket);
		    
				NDIS_SET_PACKET_STATUS(Adapter->LdnRecvPacket, NDIS_STATUS_RESOURCES);
				NDIS_SET_PACKET_HEADER_SIZE(Adapter->LdnRecvPacket, ETH_HEADER_SIZE);
  
  			PacketArray[0]=Adapter->LdnRecvPacket;
				NdisMIndicateReceivePacket(
            Adapter->AdapterHandle,
            PacketArray,
            1);
	
		    NdisAdjustBufferLength(Adapter->LdnRecvPacketBuffer, NIC_BUFFER_SIZE);
		}
		
    //NdisReleaseSpinLock(&Adapter->RecvLock);

    
    MP_DEC_REF(Adapter);
    DEBUGP(MP_TRACE, ("<---NICIndicateReceiveTimerDpc\n"));    
}


VOID 
NICFreeRecvPacket(
    PMP_ADAPTER Adapter,
    PNDIS_PACKET Packet)
/*++

Routine Description:

    Adapter    - pointer to the adapter structure
    Packet      - pointer to the receive packet
        
Arguments:

    This is called by MPReturnPacket to free the Receive packet
    indicated above. Since we have used the send-side TCB, we 
    will also carefully complete the pending SendPacket if we are 
    the last one to use the TCB buffers.
    
Return Value:

    VOID

--*/
{

    PTCB pTCB = *(PTCB *)Packet->MiniportReserved;
    PMP_ADAPTER SendAdapter = (PMP_ADAPTER)pTCB->Adapter;
    PNDIS_PACKET SendPacket = pTCB->OrgSendPacket;    
    PLIST_ENTRY pEntry;
    
    DEBUGP(MP_TRACE, ("--> NICFreeRecvPacket\n"));
    DEBUGP(MP_INFO, ("Adapter= %p FreePkt= %p Ref=%d\n", 
                            SendAdapter, SendPacket, pTCB->Ref));

    ASSERT(pTCB->Ref > 0);
    ASSERT(Adapter);


/*    //
    // Put the packet back in the free list for reuse.
    //
    NdisAcquireSpinLock(&Adapter->RecvLock);    

    InsertTailList(
        &Adapter->RecvFreeList, 
        (PLIST_ENTRY)&Packet->MiniportReserved[0]);
    
    Adapter->nBusyRecv--;     
    ASSERT(Adapter->nBusyRecv >= 0);
    
    NdisReleaseSpinLock(&Adapter->RecvLock);    

    //
    // Check to see whether we are the last one to use the TCB
    // by decrementing the refcount. If so, complete the pending
    // Send packet and free the TCB block for reuse.
    // 
    if(NdisInterlockedDecrement(&pTCB->Ref) == 0)
    {
        Adapter->GoodTransmits++;

        NdisMSendComplete(
            SendAdapter->AdapterHandle,
            SendPacket,
            NDIS_STATUS_SUCCESS);
    
        NICFreeSendTCB(SendAdapter, pTCB);
        //
        // Before we exit, since we have the control, let use see if there any 
        // more packets waiting in the queue to be sent.
        //
        if(MP_IS_READY(SendAdapter))
        {
            pEntry = (PLIST_ENTRY) NdisInterlockedRemoveHeadList(
                            &SendAdapter->SendWaitList, 
                            &SendAdapter->SendLock);
            if(pEntry)
            {
                SendPacket = CONTAINING_RECORD(pEntry, NDIS_PACKET, MiniportReserved);
                NICSendPacket(SendAdapter, SendPacket);             
            }
        }
    }*/

    DEBUGP(MP_TRACE, ("<-- NICFreeRecvPacket\n"));
}





BOOLEAN
NICIsPacketTransmittable(
    PMP_ADAPTER Adapter,
    PNDIS_PACKET Packet
    )
/*++

Routine Description:

    This routines checks to see whether the packet can be accepted
    for transmission based on the currently programmed filter type 
    of the NIC and the mac address of the packet.
    
Arguments:

    Adapter    - pointer to the adapter structure
    Packet      - pointer to the send packet


Return Value:

    True or False

--*/
{
    INT               Equal;            
    UINT              PacketLength;
    PNDIS_BUFFER      FirstBuffer = NULL;
    PUCHAR            Address = NULL;
    UINT              CurrentLength;
    ULONG             index;
    BOOLEAN           result = FALSE;
    
    DEBUGP(MP_LOUD, 
        ("DestAdapter=%p, PacketFilter = 0x%08x\n", 
        Adapter,
        Adapter->PacketFilter));

    
    do {

#ifdef NDIS51_MINIPORT
       NdisGetFirstBufferFromPacketSafe(
            Packet,
            &FirstBuffer,
            &Address,
            &CurrentLength,
            &PacketLength,
            NormalPagePriority);
#else
       NdisGetFirstBufferFromPacket(
            Packet,
            &FirstBuffer,
            &Address,
            &CurrentLength,
            &PacketLength);
#endif
        if(!Address){
            break;
        }
        

        DEBUGP(MP_LOUD, ("Dest Address = %02x-%02x-%02x-%02x-%02x-%02x\n", 
                    Address[0], Address[1], Address[2],
                    Address[3], Address[4], Address[5]));
        
        //
        // If the NIC is in promiscuous mode, we will transmit anything
        // and everything.
        //
        if(Adapter->PacketFilter & NDIS_PACKET_TYPE_PROMISCUOUS) {
            result = TRUE;
            break;
        } 
        else if(ETH_IS_BROADCAST(Address)) {
            //
            // If it's a broadcast packet, check our filter settings to see
            // we can transmit that.
            //
            if(Adapter->PacketFilter & NDIS_PACKET_TYPE_BROADCAST) {
                result = TRUE;
                break;
            }
        }
        else if(ETH_IS_MULTICAST(Address)) {
            //
            // If it's a multicast packet, check our filter settings to see
            // we can transmit that.
            //
            if(Adapter->PacketFilter & NDIS_PACKET_TYPE_ALL_MULTICAST) {
                result = TRUE;
                break;
            }
            else if(Adapter->PacketFilter & NDIS_PACKET_TYPE_MULTICAST) {
                //
                // Check to see if the multicast address is in our list
                //
                Equal = (UINT)-1;
                for(index=0; index <  Adapter->ulMCListSize; index++) {
                    ETH_COMPARE_NETWORK_ADDRESSES_EQ(
                        Address,
                        Adapter->MCList[index], 
                        &Equal);
                    if(Equal == 0){ // 0 Implies equality
                        result = TRUE;
                        break;
                    }
                }
                if(Equal == 0){ // 0 Implies equality
                    result = TRUE;
                    break;
                }
            }
        }
        else if(Adapter->PacketFilter & NDIS_PACKET_TYPE_DIRECTED) {
            //
            // This has to be a directed packet. If so, does packet source 
            // address match with the mac address of the NIC.
            // 
            ETH_COMPARE_NETWORK_ADDRESSES_EQ(
                Address,
                Adapter->CurrentAddress, 
                &Equal);
            if(Equal == 0){
                result = TRUE;
                break;
            }
        }
        //
        // This is a junk packet. We can't transmit this.
        //
        result = FALSE;
        
    }while(FALSE);
    
    return result;
}

