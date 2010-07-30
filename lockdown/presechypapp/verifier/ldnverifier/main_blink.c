/** @file
  main program
  Project Includes:
  	LedBlink on P1.24 - Morse Code 
 		Serial Terminal Communication 115200kbd
 		Printf on Serial Console
 		Micro Command Interpretter 
 		Loop Toggle P0.5 Pin
 		1sec Heart Beat
 Copyright Digital Shortcut 2008 **/


#include "console.h"

#include "lpc21xx.h"
#include "timerC.h"          	// timer functions

//[USB]
#include "type.h"
#include "usbdebug.h"
#include "usbapi.h"

//[USB]
#define BULK_IN_EP		0x82
#define BULK_OUT_EP		0x05



#define MAX_PACKET_SIZE	64

#define LE_WORD(x)		((x)&0xFF),((x)>>8)

#define SIMHOST_GET_OPSTATUS			0x10
#define SIMHOST_GET_BUTTONSTATUS  0x11
#define SIMHOST_SET_LEDSTATUS			0x12


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
	LE_WORD(0x20),  		// wTotalLength
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
	0x02,   				// bNumEndPoints
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

// bulk out
	0x07,   		
	DESC_ENDPOINT,   		
	BULK_OUT_EP,			// bEndpointAddress
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


volatile unsigned int	Event; // for timer


#define LF	10
#define CR	13

#define BAUD_RATE	115200


// external prototypes
//extern	int printf(const char *format, ...);
extern	int sprintf(char *out, const char *format, ...);
extern	void Init2148(void);

// Forward Prototypes
void 	InitGPIO(void);

//initialize LPC2148 GPIO pins
void InitGPIO(void){
  // Initialize P0.7 .. P0.0
  PINSEL0   &= 0x000000FF;		// P0.7 .. P0.0 GPIOs
  FIO0DIR   |= 0x0000007F;		// P0.6 .. P0.0 Output
  FIO0CLR    = 0x0000007F;		// "0" on P0.0.. P0.6
	
}    

//------------------------------------------------------------------------------
//LED on/off functionality

//RED LED at P0.6
//GREEN LED at P0.3

void RedLed_On(void){
	FIO0SET = 0x40;			//P0.6 = 1
}

void RedLed_Off(void){
	FIO0CLR = 0x40;			//P0.6 = 0
}

void GreenLed_On(void){
	FIO0SET = 0x8;			//P0.3 = 1
}

void GreenLed_Off(void){
	FIO0CLR = 0x8;			//P0.3 = 0
}

void msec_delay(unsigned int msecs){
	unsigned int t_msecs=0;
	while(1){
		if(Event){
			Event=0;
			t_msecs++;
		}
		
		if(t_msecs > msecs)
			break;
	}
}

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
//BUTTON CODE
//button connected to P0.7
int buttonpressed(void){
	unsigned int value;
	
	value = FIO0PIN & 0x80; //P0.7 status
	//printf("value=%u\n", value);
	return value;
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
		printf("SET_LEDSTATUS:\n");
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
			if(buttonpressed())
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
		
	default:
		printf("Unhandled request %X\n", pSetup->bRequest);
		return FALSE;
	}
	return TRUE;
}
			


 
/*************************************************************************
	main
	====
**************************************************************************/




//------------------------------------------------------------------------------
//wiznet chipset initialization
void init_wiznet(void){
  


}


//------------------------------------------------------------------------------



int main(void)
{
	// PLL and MAM
	Init2148();

	// init console Baud Rate 115200kbd
	ConsoleInit(60000000 / (16 * BAUD_RATE));
	
	printf("Lockdown verifier...\n");
	printf("Author: Amit Vasudevan (amitvasudevan@acm.org)\n");
	
	timerInit();
	Event=0;
	
	InitGPIO();

#if 0
	printf("Doing LED blinking\n");
	while(1){
		blinkledsalternate();
		msec_delay(100);
	}
#endif

#if 0
	printf("Doing BUTTON test..\n");
	while(1){
		if(buttonpressed())
			printf("PRESSED\n");
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
	USBHwRegisterEPIntHandler(BULK_IN_EP, _HandleBulkIn);
	USBHwRegisterEPIntHandler(BULK_OUT_EP, _HandleBulkOut);

	printf("Starting USB communication\n");

	// connect to bus
	USBHwConnect(TRUE);

	// call USB interrupt handler continuously
	while (1) {
		USBHwISR();
		
		//lockdown verifier logic
		switch(devicestate){
		 	case STATE_WAIT_UNTRUSTED:
			handle_state_wait_untrusted();
			break;

			case STATE_WAIT_TRUSTED:
			handle_state_wait_trusted();
			break;

			case STATE_WAIT_TRANSITION:
			GreenLed_Off();
			RedLed_On();
      handle_state_wait_transition();
			break;
	
			default:
			break;
		}
		
		
	}
#endif
	
	return 0;
}
