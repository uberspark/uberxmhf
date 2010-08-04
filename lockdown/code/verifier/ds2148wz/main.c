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
		
	default:
		printf("Unhandled request %X\n", pSetup->bRequest);
		return FALSE;
	}
	return TRUE;
}

//---wiznet network chipset interfaces------------------------------------------
// the following variables are referenced by the core wiznet/ds2148 
// implementation
int		CRdyMax=0, SpurIntCnt=0;
int		W53ErFlg=0, sCRcnt=0, Tst1Flag=0;
uint8					EstbPhase[MAX_SOCK_NUM];
#define testR	0x21a //test register 

uint8 tx_mem_conf[8] = { 8, 8, 8, 8, 8, 8, 8, 8};  				// for setting TMSR, all socket TxBufs-14k 
uint8 rx_mem_conf[8] = { 8, 8, 8, 8, 8, 8, 8, 8};         // for setting RMSR, all socket RxBufs-2k  

uint8 ip[4] = {192,168,2,66};                  	// IP address, for setting SIP register
uint8 gw[4] = {192,168,2,1};                     	// Gateway address, for setting GAR register 
uint8 sn[4] = {255,255,255,0};                    // Subnet mask, for setting SUBR register
uint8 mac[6] = {0x06,0x44,0x53,0x06,0x06,0x06};    			// Our MAC address

			
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
	
	timerInit();
	Event=0;
	
	InitGPIO();
	
  //get the current switch state on the verifier and bail out
  //if there is a h/w problem
  ldnverifier_switchstate = ldnverifier_getswitchstatus();
  if(ldnverifier_switchstate == LDN_SWITCH_INVALID){
    printf("\nFatal error: Invalid switch state, HALT!");
    magnetron_amberled_on();
    while(1);
  }


#if 1
  printf("Doing network testing...\n");
  ldnverifier_netif_initialize();
  

  printf("Done.\n");
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
	
#if 0	//USB code

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
			handle_state_wait_transition();
			break;
	
			default:
			break;
		}
		
		
	}
#endif
	
	return 0;
}
