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

// lockdown verifier implementation main module
// author: amit vasudevan(amitvasudevan@acm.org)


#include "type.h"

#include "console.h"
#include "lpc21xx.h"
#include "timerC.h"          	// timer functions
//[USB]
#include "usbdebug.h"
#include "usbapi.h"
//[Wiznet]
#include "include_netif/ds5300.h"
#include "include_netif/w5300.h"
#include "include_netif/socket.h"


//[USB]
#define BULK_IN_EP		0x82
//#define BULK_OUT_EP		0x05
#define NETIF_SEND_EP	0x05
#define NETIF_RECV_EP	0x84


#define NETIF_MAX_FRAMESIZE	(512)
#define MAX_PACKET_SIZE	64
#define LE_WORD(x)		((x)&0xFF),((x)>>8)


static const U8 abDescriptors[] = {

/* Device descriptor */
	0x12,              		
	DESC_DEVICE,       		
	LE_WORD(0x0200),		// bcdUSB	
	0xFF,              		// bDeviceClass
	0x00,              		// bDeviceSubClass
	0x00,              		// bDeviceProtocol
	MAX_PACKET_SIZE0,  		// bMaxPacketSize
	LE_WORD(0xFFFF),		// idVendor
	LE_WORD(0x0004),		// idProduct
	LE_WORD(0x0100),		// bcdDevice
	0x01,              		// iManufacturer
	0x02,              		// iProduct
	0x03,              		// iSerialNumber
	0x01,              		// bNumConfigurations

// configuration
	0x09,
	DESC_CONFIGURATION,
	LE_WORD(0x27),  		// wTotalLength
	0x01,  					// bNumInterfaces
	0x01,  					// bConfigurationValue
	0x00,  					// iConfiguration
	0x80,  					// bmAttributes
	0x32,  					// bMaxPower

// interface
	0x09,   				
	DESC_INTERFACE, 
	0x00,  		 			// bInterfaceNumber
	0x00,   				// bAlternateSetting
	0x03,   				// bNumEndPoints
	0xFF,   				// bInterfaceClass
	0x00,   				// bInterfaceSubClass
	0x00,   				// bInterfaceProtocol
	0x00,   				// iInterface

// bulk in
	0x07,   		
	DESC_ENDPOINT,   		
	BULK_IN_EP,				// bEndpointAddress
	0x02,   				// bmAttributes = BULK
	LE_WORD(MAX_PACKET_SIZE),// wMaxPacketSize
	0,						// bInterval   		

// netif SEND (bulk-out) endpoint
	0x07,   		
	DESC_ENDPOINT,   		
	NETIF_SEND_EP,				// bEndpointAddress
	0x02,   				// bmAttributes = BULK
	LE_WORD(MAX_PACKET_SIZE),// wMaxPacketSize
	0,						// bInterval   		

// netif RECV (bulk-in) endpoint
	0x07,   		
	DESC_ENDPOINT,   		
	NETIF_RECV_EP,				// bEndpointAddress
	0x02,   				// bmAttributes = BULK
	LE_WORD(MAX_PACKET_SIZE),// wMaxPacketSize
	0,						// bInterval   		


// string descriptors
	0x04,
	DESC_STRING,
	LE_WORD(0x0409),

	// manufacturer string
	0x0E,
	DESC_STRING,
	'L', 0, 'P', 0, 'C', 0, 'U', 0, 'S', 0, 'B', 0,

	// product string
	0x1A,
	DESC_STRING,
	'M', 0, 'e', 0, 'm', 0, 'o', 0, 'r', 0, 'y', 0, 'A', 0, 'c', 0, 'c', 0, 'e', 0, 's', 0, 's', 0,

	// serial number string
	0x12,
	DESC_STRING,
	'D', 0, 'E', 0, 'A', 0, 'D', 0, 'C', 0, '0', 0, 'D', 0, 'E', 0,
	
	// terminator
	0
};


typedef struct {
	U32		dwAddress;
	U32		dwLength;
} TMemoryCmd;


static TMemoryCmd	MemoryCmd;
static U8			abVendorReqData[sizeof(TMemoryCmd)];
//-----------------------------------------------------------------------------

uint16 netif_sendframe(unsigned char *sendbuf, uint16 length);
uint16 netif_recvnextframe(unsigned char *recvbuf, uint16 length);



//volatile unsigned int	Event; // for timer


#define LF	10
#define CR	13

#define BAUD_RATE	115200


extern	int sprintf(char *out, const char *format, ...);
extern	void Init2148(void);

// Forward Prototypes
void 	InitGPIO(void);

/*
Digital Shortcut Proprietary Interface: LPC2148 to WZ5300

	LPC2148																			 ___________							WizNet5300
																							|						|
		P1.16-------------------AD0-------------->|2				19|-------------> WizAddr0
																							|						|
		P1.17-------------------AD1-------------->|3				18|-------------> WizAddr1
																							|						|
		P1.18-------------------AD2-------------->|4				17|-------------> WizAddr2
																							|						|
		P1.19-(WIZ_WR)----------WD3-------------->|5				16|-------------> WizWr_L
																							|						|
		P1.20-(WIZ_RD)----------RD4-------------->|6				15|-------------> WizRd_L
																							|						|
		P1.21-(WIZ_RES)---------RsD5------------->|7				14|-------------> WizRes_L
																							|						|
																							|	 74C573		|
																							|						|
		P1.23-(WIZ_ON)----------SD7-------------->|9				12|-------------> WizPwrOn
																							|						|
																							|						|
		P1.24-(LATCH)-----------WLD---|>o---------|11					|
																							|___________|

		P1.25-(WIZ_CS)----------------|>o----------------------------------->	WizCS_L	
		
  Startup Defaults: WLD=0, WIZ_ON=1, WIZ_RES=1, WIZ_CS=0; WIZ_WR=1; WIZ_RD=1;																							
*/

//initialize LPC2148 GPIO pins
void InitGPIO(void){
  
  PINSEL0   &= 0x700600FF;		// P0.7 .. P0.0 , P0.17, P0.18 P0.28-P0.30 GPIOs
  FIO0DIR   |= 0x7000007F;		// P0.6 .. P0.0 , P0.28-P0.30 Output
  FIO0CLR    = 0x7000007F;		// "0" on P0.0.. P0.6, P0.28-P0.30
	
	P1Init();
}    

//------------------------------------------------------------------------------
//LED on/off functionality

//magnetron red led at P0.28
//magnetron green led at P0.29
//magnetron amber led at P0.30

void magnetron_redled_on(void){
  FIO0SET = 0x10000000; //P0.28=1
}

void magnetron_redled_off(void){
  FIO0CLR = 0x10000000; //P0.28=0
}

void magnetron_greenled_on(void){
  FIO0SET = 0x20000000; //P0.29=1;
}

void magnetron_greenled_off(void){
  FIO0CLR = 0x20000000; //P0.29=0;
}

void magnetron_amberled_on(void){
  FIO0SET = 0x40000000; //P0.30=1;
}

void magnetron_amberled_off(void){
  FIO0CLR = 0x40000000; //P0.30=0
}

#define RedLed_On magnetron_redled_on
#define RedLed_Off magnetron_redled_off
#define GreenLed_On magnetron_greenled_on
#define GreenLed_Off magnetron_greenled_off


/*void msec_delay(unsigned int msecs){
	unsigned int t_msecs=0;
	while(1){
		if(Event){
			Event=0;
			t_msecs++;
		}
		
		if(t_msecs > msecs)
			break;
	}
}*/
}*/

unsigned int isredon=0;
//test blink green and red led alternatively
void blinkledsalternate(void){
	if(!isredon){
		RedLed_On();
		GreenLed_Off();
		isredon=1;
	}else{
		RedLed_Off();
		GreenLed_On();
		isredon=0;
	}

}


//-----------------------------------------------------------------------------
//switch interface
//switch connected to P0.17 and P0.18
//P0.17   P0.18 State
//0        1     Insecure
//1        0     Secure
//0        0     Invalid
//1        1     Invalid

#define LDN_SWITCH_SECURE   0x1
#define LDN_SWITCH_INSECURE 0x2
#define LDN_SWITCH_INVALID  0x3

int ldnverifier_getswitchstatus(void){
	unsigned long int status;
	
	status = FIO0PIN & 0x00060000;
	
	if(status == 0x00040000)
	 return LDN_SWITCH_INSECURE;
	else if(status == 0x00020000)
	 return LDN_SWITCH_SECURE;
	else
	 return LDN_SWITCH_INVALID;
}

volatile int ldnverifier_switchstate = LDN_SWITCH_INVALID;

//---tells us if the user flipped switch----------------------------------------
//returns 1 if switch was flipped else 0
int ldnverifier_isswitchflipped(void){
  int current_switchstate;
  
  //get the current switch state on the verifier and account
  //for bounce
  do{
    current_switchstate = ldnverifier_getswitchstatus();
  }while(current_switchstate == LDN_SWITCH_INVALID);
  
  if(current_switchstate != ldnverifier_switchstate){
    ldnverifier_switchstate = current_switchstate;
    printf("\nswitch flipped!");
    return 1;
  }else{
    return 0;
  }
  
}

//
#define	STATE_WAIT_TRUSTED		0x1
#define	STATE_WAIT_UNTRUSTED	0x2
#define STATE_WAIT_TRANSITION	0x3

#define OP_START			0x1
#define OP_TRUSTED		0x2
#define OP_UNTRUSTED	0x3

unsigned char devicestate=STATE_WAIT_TRANSITION;
unsigned char operationstatus = OP_START;

void handle_state_wait_trusted(void){
	//Turn ON green led and turn OFF red led
  RedLed_Off();
	GreenLed_On();
}

void handle_state_wait_untrusted(void){
	//Turn ON red led and turn OFF green led
	RedLed_On();
	GreenLed_Off();
}

int state_wait_transition_counter=0;
int state_wait_transition_flip=0;

void handle_state_wait_transition(void){
	//turn off green LED
	GreenLed_Off();
  
  state_wait_transition_counter++;
	if(state_wait_transition_counter < 50000)
		return;
	
	state_wait_transition_counter=0;

	if(state_wait_transition_flip == 0){
		//Turn OFF red led
		RedLed_Off();
		state_wait_transition_flip=1;
	}else{
	   //Turn ON red led
		RedLed_On();
    state_wait_transition_flip=0;
	}
}



//[USB]

static void _HandleBulkIn(U8 bEP, U8 bEPStatus)
{
	int iChunk;
	
	iChunk = MIN(MAX_PACKET_SIZE, MemoryCmd.dwLength);
	if (iChunk == 0) {
		DBG("done\n");
		return;
	}
	
	// send next part
	USBHwEPWrite(bEP, (U8 *)MemoryCmd.dwAddress, iChunk);
	
	MemoryCmd.dwAddress += iChunk;
	MemoryCmd.dwLength -= iChunk;

	// limit address range to prevent abort
	MemoryCmd.dwAddress &= ~(-512 * 1024);
}


static void _HandleBulkOut(U8 bEP, U8 bEPStatus)
{
	int iChunk;
	
	// get next part
	iChunk = USBHwEPRead(bEP, NULL, 0);
	
	MemoryCmd.dwAddress += iChunk;
	MemoryCmd.dwLength -= iChunk;	

	if (MemoryCmd.dwLength == 0) {
		DBG("done\n");
	}
}

#define ETH_MTU	1500
#define ETH_PACKETSIZE (ETH_MTU+14)


#if 0
static uint32 txframesize=0;
unsigned char txframe[ETH_PACKETSIZE];

static void _HandleNETIFSend(U8 bEP, U8 bEPStatus){
	int iChunk;
	printf("%s: got control\n", __FUNCTION__);

  iChunk = USBHwEPRead(bEP, (unsigned char *)((uint32)&txframe + txframesize), MAX_PACKET_SIZE);

	iChunk = USBHwEPRead(bEP, (unsigned char *)((uint32)&txframe + txframesize), MAX_PACKET_SIZE);
	//printf(" read %u byte chunk\n", iChunk);
	txframesize += iChunk;
	//printf(" txtframesize=%u\n", txframesize);

 	if(txframesize >= ETH_PACKETSIZE){
		//sanity check
		if(txframesize != ETH_PACKETSIZE){
			printf("%s: FATAL, we lost USB packets (%u)???\n", __FUNCTION__, txframesize);
			while(1);
		}

    //
    //printf(" read frame of %u bytes, xmit..\n", txframesize);
    //TODO:xmit
    netif_sendframe(&txframe, txframesize);
		txframesize=0;
	} 

}
#else

static uint32 tx_in_progress=0;	//1 if we are pulling TX frame from host, else 0
static uint32 txframesize=0;	//size of the TX frame that host will offer us 
unsigned char txframe[ETH_PACKETSIZE]; //if above is non-zero the actual TX frame data
static uint32 txframeoffset=0;	//since we pull in 64 byte chunks, we need to maintain the next offset

static void _HandleNETIFSend(U8 bEP, U8 bEPStatus){
	int iChunk;
	//printf("%s got control...\n", __FUNCTION__);

	if(tx_in_progress){ //we only pull the TX packet if there is one 
  	if(txframesize - txframeoffset < MAX_PACKET_SIZE){
  		USBHwEPRead(bEP, (unsigned char *)((uint32)&txframe + txframeoffset), (txframesize-txframeoffset) );
			txframeoffset = txframesize;
		}else{
			USBHwEPRead(bEP, (unsigned char *)((uint32)&txframe + txframeoffset), MAX_PACKET_SIZE);
			txframeoffset+= MAX_PACKET_SIZE;
		}
		
		//check if we are done with the packet
		if(txframeoffset >= txframesize){
			//xmit the packet
	    netif_sendframe(&txframe, txframesize);
			txframeoffset=0;
		  tx_in_progress=0;
		}
	}  


}



#endif

static uint32 rx_in_progress=0;	//1 if host is pulling out RX frame from us, else 0
static uint32 rxframesize=0;	//size of the RX frame that host will pull 
unsigned char rxframe[ETH_PACKETSIZE]; //if above is non-zero the actual RX frame data
static uint32 rxframeoffset=0;	//since we serve in 64 byte chunks, we need to maintain the next offset

static void _HandleNETIFRecv(U8 bEP, U8 bEPStatus){
	int iChunk;
	
	if(rx_in_progress){ //we only serve the RX packet if there is one 
	  //printf("%s got control...\n", __FUNCTION__);

  	if(rxframesize - rxframeoffset < MAX_PACKET_SIZE){
  		USBHwEPWrite(bEP, (unsigned char *)((uint32)&rxframe + rxframeoffset), (rxframesize-rxframeoffset) );
			rxframeoffset = rxframesize;
		}else{
			USBHwEPWrite(bEP, (unsigned char *)((uint32)&rxframe + rxframeoffset), MAX_PACKET_SIZE);
			rxframeoffset+= MAX_PACKET_SIZE;
		}
		
		//check if we are done with the packet
		if(rxframeoffset >= rxframesize){
			rxframeoffset=0;
		  rx_in_progress=0;
		}
	}  
}


unsigned char tempbuffer[0x40];
unsigned char bufferbuttonstatus[0x30];

						
/*************************************************************************
	HandleVendorRequest
	===================
		Handles vendor specific requests
		
	Control transfer fields:
	* request:	0x01 = prepare memory read
				0x02 = prepare memory write
	* index:	ignored
	* value:	ignored
	* data:		U32 dwAddress
				U32 dwLength
		
**************************************************************************/
static BOOL HandleVendorRequest(TSetupPacket *pSetup, int *piLen, U8 **ppbData)
{
	TMemoryCmd	*pCmd;
	U8      *pbData = *ppbData;
	
	pCmd = (TMemoryCmd *)*ppbData;

	switch (pSetup->bRequest) {
	
	// prepare read
	case 0x01:
		MemoryCmd = *pCmd;
		printf("READ: addr=%X, len=%d\n", MemoryCmd.dwAddress, MemoryCmd.dwLength);
		// send initial packet
		_HandleBulkIn(BULK_IN_EP, 0);
		*piLen = 0;
		break;
		
	// prepare write
	case 0x02:
		MemoryCmd = *pCmd;
		printf("WRITE: addr=%X, len=%d\n", MemoryCmd.dwAddress, MemoryCmd.dwLength);
		*piLen = 0;
		break;

	case 0xB0: //set led command
		printf("Command: Set LED\n");
		memcpy(&tempbuffer, pbData, 0x40);
		//printf("tempbuffer[0]=%x, tempbuffer[1]=%x\n", tempbuffer[0], tempbuffer[1]);
		if(tempbuffer[0] == 1){
			devicestate=STATE_WAIT_TRUSTED;
			operationstatus=OP_UNTRUSTED;	//on a switch we need to go to untrusted
		}else{
			devicestate=STATE_WAIT_UNTRUSTED;
			operationstatus=OP_TRUSTED;	//on a switch we need to go to trusted
		}	
		*piLen=0;
		break;
		
	case 0xA0:	//get button status
		{
			unsigned char buttonstatus=0;
			//printf("GET_BUTTONSTATUS:\n");
			if(ldnverifier_isswitchflipped())
				buttonstatus=1;
		  else
				buttonstatus=0;

			if(buttonstatus == 1)
				devicestate = STATE_WAIT_TRANSITION;

			memset(bufferbuttonstatus, 0, sizeof(bufferbuttonstatus));
			bufferbuttonstatus[0]=buttonstatus;
			//printf("bufferbuttonstatus[0]=%x\n", bufferbuttonstatus[0]);
			//memcpy(pbData, bufferbuttonstatus, sizeof(bufferbuttonstatus));
   		//*piLen = 0x40;
			USBHwEPWrite(BULK_IN_EP, (unsigned char *)bufferbuttonstatus, 0x1);
   		*piLen =1;
   	}   		
   	break;   	


	case 0xF0:	//read packet command
		{
   		if(!rx_in_progress){ //we ignore the command if rx_in_progress = 1
  		 	rxframesize = (uint32)netif_recvnextframe(&rxframe, ETH_PACKETSIZE);
   		 	USBHwEPWrite(NETIF_RECV_EP, (unsigned char *)&rxframesize, sizeof(uint32));
   		 	if(rxframesize){
					rx_in_progress=1; // we have a RX packet to offer, host will now pull RX frame from us
			    printf("<Packet READ, %u bytes payload\n", rxframesize);
			   }
   			

      }	
			*piLen = 0;
   	}   		
   	break;   	


	case 0xE0:	//send packet command
		{
   		if(!tx_in_progress){ //we ignore the command if tx_in_progress = 1
  		 	txframesize = pCmd->dwLength;
   		 	if(txframesize)
					tx_in_progress=1; // we have a TX packet to pull from host
			 
   			printf(">Packet SEND, %u bytes payload\n", pCmd->dwLength);

      }	
			*piLen = 0;
   	}   		
   	break;   	

		
	default:
		printf("Unhandled request %X\n", pSetup->bRequest);
		return FALSE;
	}
	return TRUE;
}

//---crc32 routine--------------------------------------------------------------
  /*-
  * ============================================================= 
  *  COPYRIGHT (C) 1986 Gary S. Brown.  You may use this program, or       
  *  code or tables extracted from it, as desired without restriction.     
  *                                                                        
  *  First, the polynomial itself and its table of feedback terms.  The    
  *  polynomial is                                                         
  *  X^32+X^26+X^23+X^22+X^16+X^12+X^11+X^10+X^8+X^7+X^5+X^4+X^2+X^1+X^0   
  *                                                                        
  *  Note that we take it "backwards" and put the highest-order term in    
  *  the lowest-order bit.  The X^32 term is "implied"; the LSB is the     
  *  X^31 term, etc.  The X^0 term (usually shown as "+1") results in      
  *  the MSB being 1.                                                      
  *                                                                        
  *  Note that the usual hardware shift register implementation, which     
  *  is what we're using (we're merely optimizing it by doing eight-bit    
  *  chunks at a time) shifts bits into the lowest-order term.  In our     
  *  implementation, that means shifting towards the right.  Why do we     
  *  do it this way?  Because the calculated CRC must be transmitted in    
  *  order from highest-order term to lowest-order term.  UARTs transmit   
  *  characters in order from LSB to MSB.  By storing the CRC this way,    
  *  we hand it to the UART in the order low-byte to high-byte; the UART   
  *  sends each low-bit to hight-bit; and the result is transmission bit   
  *  by bit from highest- to lowest-order term without requiring any bit   
  *  shuffling on our part.  Reception works similarly.                    
  *                                                                        
  *  The feedback terms table consists of 256, 32-bit entries.  Notes:     
  *                                                                        
  *      The table can be generated at runtime if desired; code to do so   
  *      is shown later.  It might not be obvious, but the feedback        
  *      terms simply represent the results of eight shift/xor opera-      
  *      tions for all combinations of data and CRC register values.       
  *                                                                        
  *      The values must be right-shifted by eight bits by the "updcrc"    
  *      logic; the shift must be unsigned (bring in zeroes).  On some     
  *      hardware you could probably optimize the shift in assembler by    
  *      using byte-swap instructions.                                     
  *      polynomial $edb88320                                              
  *                                                                        
  *  --------------------------------------------------------------------  */

static unsigned long crc32_tab[] = {
      0x00000000L, 0x77073096L, 0xee0e612cL, 0x990951baL, 0x076dc419L,
      0x706af48fL, 0xe963a535L, 0x9e6495a3L, 0x0edb8832L, 0x79dcb8a4L,
      0xe0d5e91eL, 0x97d2d988L, 0x09b64c2bL, 0x7eb17cbdL, 0xe7b82d07L,
      0x90bf1d91L, 0x1db71064L, 0x6ab020f2L, 0xf3b97148L, 0x84be41deL,
      0x1adad47dL, 0x6ddde4ebL, 0xf4d4b551L, 0x83d385c7L, 0x136c9856L,
      0x646ba8c0L, 0xfd62f97aL, 0x8a65c9ecL, 0x14015c4fL, 0x63066cd9L,
      0xfa0f3d63L, 0x8d080df5L, 0x3b6e20c8L, 0x4c69105eL, 0xd56041e4L,
      0xa2677172L, 0x3c03e4d1L, 0x4b04d447L, 0xd20d85fdL, 0xa50ab56bL,
      0x35b5a8faL, 0x42b2986cL, 0xdbbbc9d6L, 0xacbcf940L, 0x32d86ce3L,
      0x45df5c75L, 0xdcd60dcfL, 0xabd13d59L, 0x26d930acL, 0x51de003aL,
      0xc8d75180L, 0xbfd06116L, 0x21b4f4b5L, 0x56b3c423L, 0xcfba9599L,
      0xb8bda50fL, 0x2802b89eL, 0x5f058808L, 0xc60cd9b2L, 0xb10be924L,
      0x2f6f7c87L, 0x58684c11L, 0xc1611dabL, 0xb6662d3dL, 0x76dc4190L,
      0x01db7106L, 0x98d220bcL, 0xefd5102aL, 0x71b18589L, 0x06b6b51fL,
      0x9fbfe4a5L, 0xe8b8d433L, 0x7807c9a2L, 0x0f00f934L, 0x9609a88eL,
      0xe10e9818L, 0x7f6a0dbbL, 0x086d3d2dL, 0x91646c97L, 0xe6635c01L,
      0x6b6b51f4L, 0x1c6c6162L, 0x856530d8L, 0xf262004eL, 0x6c0695edL,
      0x1b01a57bL, 0x8208f4c1L, 0xf50fc457L, 0x65b0d9c6L, 0x12b7e950L,
      0x8bbeb8eaL, 0xfcb9887cL, 0x62dd1ddfL, 0x15da2d49L, 0x8cd37cf3L,
      0xfbd44c65L, 0x4db26158L, 0x3ab551ceL, 0xa3bc0074L, 0xd4bb30e2L,
      0x4adfa541L, 0x3dd895d7L, 0xa4d1c46dL, 0xd3d6f4fbL, 0x4369e96aL,
      0x346ed9fcL, 0xad678846L, 0xda60b8d0L, 0x44042d73L, 0x33031de5L,
      0xaa0a4c5fL, 0xdd0d7cc9L, 0x5005713cL, 0x270241aaL, 0xbe0b1010L,
      0xc90c2086L, 0x5768b525L, 0x206f85b3L, 0xb966d409L, 0xce61e49fL,
      0x5edef90eL, 0x29d9c998L, 0xb0d09822L, 0xc7d7a8b4L, 0x59b33d17L,
      0x2eb40d81L, 0xb7bd5c3bL, 0xc0ba6cadL, 0xedb88320L, 0x9abfb3b6L,
      0x03b6e20cL, 0x74b1d29aL, 0xead54739L, 0x9dd277afL, 0x04db2615L,
      0x73dc1683L, 0xe3630b12L, 0x94643b84L, 0x0d6d6a3eL, 0x7a6a5aa8L,
      0xe40ecf0bL, 0x9309ff9dL, 0x0a00ae27L, 0x7d079eb1L, 0xf00f9344L,
      0x8708a3d2L, 0x1e01f268L, 0x6906c2feL, 0xf762575dL, 0x806567cbL,
      0x196c3671L, 0x6e6b06e7L, 0xfed41b76L, 0x89d32be0L, 0x10da7a5aL,
      0x67dd4accL, 0xf9b9df6fL, 0x8ebeeff9L, 0x17b7be43L, 0x60b08ed5L,
      0xd6d6a3e8L, 0xa1d1937eL, 0x38d8c2c4L, 0x4fdff252L, 0xd1bb67f1L,
      0xa6bc5767L, 0x3fb506ddL, 0x48b2364bL, 0xd80d2bdaL, 0xaf0a1b4cL,
      0x36034af6L, 0x41047a60L, 0xdf60efc3L, 0xa867df55L, 0x316e8eefL,
      0x4669be79L, 0xcb61b38cL, 0xbc66831aL, 0x256fd2a0L, 0x5268e236L,
      0xcc0c7795L, 0xbb0b4703L, 0x220216b9L, 0x5505262fL, 0xc5ba3bbeL,
      0xb2bd0b28L, 0x2bb45a92L, 0x5cb36a04L, 0xc2d7ffa7L, 0xb5d0cf31L,
      0x2cd99e8bL, 0x5bdeae1dL, 0x9b64c2b0L, 0xec63f226L, 0x756aa39cL,
      0x026d930aL, 0x9c0906a9L, 0xeb0e363fL, 0x72076785L, 0x05005713L,
      0x95bf4a82L, 0xe2b87a14L, 0x7bb12baeL, 0x0cb61b38L, 0x92d28e9bL,
      0xe5d5be0dL, 0x7cdcefb7L, 0x0bdbdf21L, 0x86d3d2d4L, 0xf1d4e242L,
      0x68ddb3f8L, 0x1fda836eL, 0x81be16cdL, 0xf6b9265bL, 0x6fb077e1L,
      0x18b74777L, 0x88085ae6L, 0xff0f6a70L, 0x66063bcaL, 0x11010b5cL,
      0x8f659effL, 0xf862ae69L, 0x616bffd3L, 0x166ccf45L, 0xa00ae278L,
      0xd70dd2eeL, 0x4e048354L, 0x3903b3c2L, 0xa7672661L, 0xd06016f7L,
      0x4969474dL, 0x3e6e77dbL, 0xaed16a4aL, 0xd9d65adcL, 0x40df0b66L,
      0x37d83bf0L, 0xa9bcae53L, 0xdebb9ec5L, 0x47b2cf7fL, 0x30b5ffe9L,
      0xbdbdf21cL, 0xcabac28aL, 0x53b39330L, 0x24b4a3a6L, 0xbad03605L,
      0xcdd70693L, 0x54de5729L, 0x23d967bfL, 0xb3667a2eL, 0xc4614ab8L,
      0x5d681b02L, 0x2a6f2b94L, 0xb40bbe37L, 0xc30c8ea1L, 0x5a05df1bL,
      0x2d02ef8dL
   };

/* Return a 32-bit CRC of the contents of the buffer. */

unsigned long crc32(const unsigned char *s, unsigned int len)
{
  unsigned int i;
  unsigned long crc32val;
  
  crc32val = 0;
  for (i = 0;  i < len;  i ++)
    {
      crc32val =
	crc32_tab[(crc32val ^ s[i]) & 0xff] ^
	  (crc32val >> 8);
    }
  return crc32val;
}
//----------------------------------------------------------------------


//---wiznet network chipset interfaces------------------------------------------
// the following variables are referenced by the core wiznet/ds2148 
// implementation
int		CRdyMax=0, SpurIntCnt=0;
int		W53ErFlg=0, sCRcnt=0, Tst1Flag=0;
uint8					EstbPhase[MAX_SOCK_NUM];
#define testR	0x21a //test register 

uint8 tx_mem_conf[8] = { 8, 8, 8, 8, 8, 8, 8, 8};  				// for setting TMSR, all socket TxBufs-14k 
uint8 rx_mem_conf[8] = { 8, 8, 8, 8, 8, 8, 8, 8};         // for setting RMSR, all socket RxBufs-2k  

uint8 ip[4] = {192,168,0,66};                  	// IP address, for setting SIP register
uint8 gw[4] = {192,168,0,1};                     	// Gateway address, for setting GAR register 
uint8 sn[4] = {255,255,255,0};                    // Subnet mask, for setting SUBR register
uint8 mac[6] = {0x06,0x44,0x53,0x06,0x06,0x06};    			// Our MAC address
uint8 bmac[6] = {0xFF,0xFF,0xFF,0xFF,0xFF,0xFF};    			// broadcast MAC address

			
void debug_checknetifsetup(void){
	uint16 v1, v2, v3, v4, v5;
	
	v1 = getMR();							// expected value is 0x3800
  v2 = IINCHIP_READ(RTR);			// expected value is 0x07D0
  v3 = IINCHIP_READ(RCR);			// expected value is 0x..08
  v4 = IINCHIP_READ(IDR);

  v5 = IINCHIP_READ(testR);
  
  printf("MR=%04x RTR=%04x RCR=%02x IDR=%04x M_%x=%04x\n",
       v1, v2, (v3&0xff), v4, testR, v5);

	if ( (v1==1)&&(v2==0x7d0)&&((v3&0xff)==8)&&(v4==0x5300)&&(v5==0x1234) ) 
		printf("[TEST:OK]\n");
	else
		printf("[TEST:FAIL!!!]\n");

  //show MAC, IP, gateway and subnetmask
  { 
  	uint8	tBuf[10];
  	
    Rd5300_bl(SIPR0, &tBuf[0], 4);
    printf("IP:   %d.%d.%d.%d\n",tBuf[0],tBuf[1],tBuf[2],tBuf[3]);
    Rd5300_bl(GAR0, &tBuf[0], 4);
    printf("GAR:  %d.%d.%d.%d\n",tBuf[0],tBuf[1],tBuf[2],tBuf[3]);
    Rd5300_bl(SUBR0, &tBuf[0], 4);												 // get subnet mask address   
    printf("SUBR: %d.%d.%d.%d\n",tBuf[0],tBuf[1],tBuf[2],tBuf[3]);
    Rd5300_bl(SHAR0, &tBuf[0], 6);
    printf("SHAR: %02x:%02x:%02x:%02x:%02x:%02x\n",tBuf[0],tBuf[1],tBuf[2],tBuf[3],tBuf[4],tBuf[5]);
 }


}  

struct arpstruct {
  unsigned char dstmac[6];
  unsigned char srcmac[6];
  unsigned char length[2];
  unsigned char payload[46];
  unsigned char fcs[4];
} __attribute__((packed));

char packetbuffer[] = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff,  //6-bytes dest MAC
                       0x06,0x44,0x53,0x06,0x06,0x06,  //6-bytes src MAC
                       0x08, 0x06,  //2-byte type (0x08,0x06 = ethernet ARP)
                       
                       //ARP packet
                       0x00, 0x01,
                       0x08, 0x00,
                       0x06,
                       0x04,
                       0x00, 0x01,
                       0x06,0x44,0x53,0x06,0x06,0x06, //our MAC address
                       0xc0, 0xa8, 0x02, 0x42,  //our IP address
                       0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  //MAC address of target 
                       0xc0, 0xa8, 0x02, 0x1E,   //IP addr of target (192.168.2.30 in our example)
                       
                       0x00,0x00,0x00,0x00,
                       0x00,0x00,0x00,0x00,
                       0x00,0x00,0x00,0x00,
                       0x00,0x00,0x00,0x00,
                       0x00,0x00,                 //18 bytes pad to get to minimum payload of 46
                       };                             
                       
unsigned char recvbuffer[1518];

//this sets socket 0 on the wiznet chipset to process raw ethernet
//frames for send and receives
void netif_setmacrawmode(void){
  int opened=0;
  uint16 value;
  
  do{
    setSn_MR(0, Sn_MR_MACRAW); //MACraw mode for socket 0
    setSn_CR(0, Sn_CR_OPEN);    //open the port
    //check if the port was open
    if ( getSn_SSR(0) == SOCK_MACRAW )
      opened=1;
    else
      setSn_CR(0, Sn_CR_CLOSE);
  }while(!opened);

  //dump contents of IMR
  value=getSn_IMR(0);
  printf("value of IMR=0x%04x\n", value);
  value=getSn_IR(0);
  printf("value of IR=0x%04x\n", value);
  

}

//---wiznet recieve a raw ethernet frame----------------------------------------
//note: this returns 0 if there are no frames to receive, else it returns
//the size of the received frame in bytes. if the received size is greater
//than length, it will return only length bytes of that frame 
uint16 netif_recvnextframe(unsigned char *recvbuf, uint16 length){
  uint32 framesize=0;
  uint16 datapacketsize;
  int numdatapacketrecords, i;
  uint16 *databufferptr = (uint16 *)recvbuf;
  
  //get the size of the next frame
  framesize = getSn_RX_RSR(0);
  
  //return 0 if there are no frames to be received
  if(!framesize)
    return 0;                                     
  
  //if framesize is greater than length, truncate frame to length bytes
  if( (framesize + 0x4) > (uint32)length)
    framesize = (uint32)length;
    
  //the format of raw frame returned by the wiznet chipset is:
  //2 bytes of DATA packet size
  //DATA packet (dest MAC, src MAC and payload excluding FCS)
  //4 bytes of FCS
  datapacketsize = getSn_RX_FIFOR(0);
  //printf("datapacketsize = %u bytes\n", datapacketsize);




#if 0  
  //calculate number of data packet records (2 bytes each) that we need
  //to gobble up from the FIFO register of socket 0
  //if data packet size is odd wiznet would have padded it to 16-bit boundary
  //adjust here if that is the case
  if(datapacketsize & 0x1)
    numdatapacketrecords = (datapacketsize + 1) / 2;
  else
    numdatapacketrecords = datapacketsize /2 ;
    
  //read the data packet into the buffer specified 
  for(i=0; i < numdatapacketrecords; i++){
    databufferptr[i] = getSn_RX_FIFOR(0);
    databufferptr[i] =  ((uint16)databufferptr[i] << 8) | ((uint16)databufferptr[i] >> 8);  
  }

  //adjust databufferptr to remove any wiznet padding in the previous step
  if(datapacketsize & 0x1){
    databufferptr = (uint16 *) ((uint32)recvbuf + ((i*2) - 1));
    framesize = (i*2) - 1;
  }else{
    databufferptr = (uint16 *) ((uint32)recvbuf + ((i*2)) );
    framesize = (i*2);
  }
    
  //read in the FCS as well
  databufferptr[1] = getSn_RX_FIFOR(0);
  databufferptr[0] = getSn_RX_FIFOR(0);
  framesize += 0x4;  
#else
  //use DS function
  {
    uint32 resultsize;
    framesize = datapacketsize + 0x4; //account for FCS
    resultsize = wiz_read_buf(0, recvbuf, framesize);
    if(resultsize != framesize){
      printf("fatal error: mismatch in resultsize and framesize!\n");
      while(1);
    }
    
    //we dont want the FCS so reduce framesize by 4
    framesize -= 0x4;
  }

#endif
  //[debug: dump our calculated CRC32 for verification]
  //{
  //  unsigned long crc;
  //  crc = crc32(recvbuf, (framesize-0x4));
  //  printf("calculated CRC-32=0x%08x\n", crc);
  //}

  //return the frame size
  return framesize;  
}

//---wiznet send a raw ethernet frame----------------------------------------
//note: this returns 0 if there is no space in the send queue, else it returns
//the size of the sent frame in bytes. length MUST be a multiple of 2! 
uint16 netif_sendframe(unsigned char *sendbuf, uint16 length){
  uint32 freespace;
  int numdatapacketrecords, i;
  uint16 *databufferptr = (uint16 *)sendbuf;
  
  //assert length is multiple of 2
  //if(length & 0x1){
  //  printf("%s: assertion failed, length is not even. HALTING!", __FUNCTION__);
  //  while(1);
  //}
  
  //get free space in TX buffer
  freespace = getSn_TX_FSR(0);
  //printf("freespace = %u bytes\n", freespace);
  //printf("length = %u bytes\n", length);
  
  //return 0 if we cannot TX at this time since TX buffer is full
  if(freespace < (uint32)length)
    return 0;

  //printf("dest mac: 0x%02x 0x%02x 0x%02x 0x%02x 0x%02x 0x%02x\n",
  //  sendbuf[0], sendbuf[1], sendbuf[2], sendbuf[3], sendbuf[4], sendbuf[5]);

#if 0  
  //calculate number of data packet records (2 bytes each) we need to
  //write to the send FIFO register
  numdatapacketrecords = length/2;
  
  //copy the frame to internal TX memory
  for(i=0; i < numdatapacketrecords; i++){
    databufferptr[i] =  ((uint16)databufferptr[i] << 8) | ((uint16)databufferptr[i] >> 8);  
    setSn_TX_FIFOR(0, databufferptr[i]);
  }
#else
  wiz_write_buf(0, sendbuf, length);

#endif
  
  //debug[] get and dump the FIFOR
  /*{
    printf("Debug dump of TXFIFO:\n");
    for(i=0; i < numdatapacketrecords; i++){
     databufferptr[i] = getSn_TX_FIFOR(0);
     databufferptr[i] =  ((uint16)databufferptr[i] << 8) | ((uint16)databufferptr[i] >> 8);  
     printf("%04x ", databufferptr[i]); 
    }
    printf("\nHalt!");
    while(1);
  }*/
  
  //set the TX size
  setSn_TX_WRSR(0, length);
  //printf("write size= 0x%08x bytes\n", getSn_TX_WRSR(0));
                       
  //xmit now
  setSn_CR(0, Sn_CR_SEND);
  
  //wait for send to complete
  {
    uint16 s0irvalue=0;
    do{
      s0irvalue = getSn_IR(0);
    } while ( (s0irvalue & Sn_IR_SENDOK) == 0 );
    setSn_IR(0, (s0irvalue & Sn_IR_SENDOK)) ;
  }

  return length;
}


			
void ldnverifier_netif_initialize(void){
  printf("\n%s:", __FUNCTION__);
  //power-on the network chipset and associated port
  W5300PwrOn();
  printf("NET: powered up chipset/port.\n");
  
  //initialize W5300 chipset and setup interrupts
  iinchip_init();			// MR_RES & MR_IND
  W5300Init2();				// Init interrupts for 5300
  printf("NET: initialized chipset and interrupts.\n");
  
  // configure internal W5300 TX/RX Memory Buffers
  if( sysinit(tx_mem_conf, rx_mem_conf)==0 ) {
    printf("FATAL: could not configure TX/RX buffers. HALTING!\n");
    while(1);
  }
  IINCHIP_WRITE(testR, 0x1234);

  printf("NET: setup TX/RX buffers.\n");              
  
  //setup MAC, IP, gateway and subnet mask
  //note: we really don't need the last three since we are going to
  //be dealing with raw ethernet frames, but they are here for now
 	setSHAR(mac); 						// MAC
  setSIPR(ip);              // IP
  setGAR(gw);               // gateway IP
  setSUBR(sn);              // subnet mask
  
  //enable IRQs
  enableIRQ();
  
  //[debug: check if all was setup correctly]
  debug_checknetifsetup();

  //enable MAC RAW mode
  printf("NET: enabling RAW MAC mode on socket 0...\n");
  netif_setmacrawmode();
  printf("NET: RAW MAC mode enabled.\n");
  
}

 
//---starting point-------------------------------------------------------------
int main(void)
{
	// PLL and MAM
	Init2148();

	// init console Baud Rate 115200kbd
	ConsoleInit(60000000 / (16 * BAUD_RATE));
	
	printf("Lockdown verifier (Magnetron)...\n");
	printf("Author: Amit Vasudevan (amitvasudevan@acm.org)\n");
	
	
	//timerInit();
	//Event=0;
	
	InitGPIO();
	
  //get the current switch state on the verifier and bail out
  //if there is a h/w problem
  ldnverifier_switchstate = ldnverifier_getswitchstatus();
  if(ldnverifier_switchstate == LDN_SWITCH_INVALID){
    printf("\nFatal error: Invalid switch state, HALT!");
    magnetron_amberled_on();
    while(1);
  }


	
  ldnverifier_netif_initialize();
	printf("NETIF initialized.\n");
  /*printf("Waiting for switch...\n");
  msec_delay(5000); //5 second wait
  printf("Done.\n");  */
  

#if 0
  printf("Doing network testing...\n");
  
  {//send frame test code
    uint16 framesize=0;
    int i;
    for(i=0; i < 1; i++){
      printf("Sending ETH/ARP frame...\n");
      do{
        framesize = netif_sendframe(&packetbuffer, sizeof(packetbuffer));
      }while(!framesize);
      printf("Sent %u bytes on the wire.\n", framesize);
    }
    

  }

    {//receive test code
    uint16 framesize=0;
    int i;
    printf("Waiting for a frame...\n");
    do{
      framesize = netif_recvnextframe(&recvbuffer, sizeof(recvbuffer));
    }while(!framesize);
    printf("Got a frame of size=%u bytes\n", framesize);
    printf("Frame contents:\n");
    for(i=0; i < framesize; i++)
      printf("0x%02x ", recvbuffer[i]);
  }


  printf("Done.\n");
  while(1);
#endif

#if 0
	printf("Doing LED blinking\n");
	while(1){
		blinkledsalternate();
		msec_delay(100);
	}
#endif

#if 0
	printf("Doing SWITCH test..\n");
	while(1){
	 unsigned int switchstatus;
	 switchstatus = ldnverifier_getswitchstatus();
	 if(switchstatus == LDN_SWITCH_SECURE)
	   printf("\nSECURE");
	 else if(switchstatus == LDN_SWITCH_INSECURE)
	   printf("\nINSECURE");
	}	
#endif	
	
#if 1	//USB code

	printf("Initialising USB stack\n");
	
	// initialise stack
	USBInit();
	
	// register device descriptors
	USBRegisterDescriptors(abDescriptors);

	// override standard request handler
	USBRegisterRequestHandler(REQTYPE_TYPE_VENDOR, HandleVendorRequest, abVendorReqData);

	// register endpoints
	//USBHwRegisterEPIntHandler(BULK_IN_EP, _HandleBulkIn);
	//USBHwRegisterEPIntHandler(BULK_OUT_EP, _HandleBulkOut);
 	USBHwRegisterEPIntHandler(NETIF_SEND_EP, _HandleNETIFSend);
 	USBHwRegisterEPIntHandler(NETIF_RECV_EP, _HandleNETIFRecv);

  //USBHwEPConfig(NETIF_SEND_EP, MAX_PACKET_SIZE);
	//USBHwEPConfig(NETIF_SEND_EP, MAX_PACKET_SIZE);
	

	printf("Starting USB communication\n");

	// connect to bus
	USBHwConnect(TRUE);

	// call USB interrupt handler continuously
	while (1) {
		USBHwISR();
		
#if 1	
		//lockdown verifier logic
		switch(devicestate){
		 	case STATE_WAIT_UNTRUSTED:
			handle_state_wait_untrusted();
			break;

			case STATE_WAIT_TRUSTED:
			handle_state_wait_trusted();
			break;

			case STATE_WAIT_TRANSITION:
			handle_state_wait_transition();
			break;
	
			default:
			break;
		}
#endif		
		
	}
#endif
	
	return 0;
}
