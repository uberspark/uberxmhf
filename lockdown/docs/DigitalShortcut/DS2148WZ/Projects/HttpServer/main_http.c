/** @file
  main program
  Project Includes: 
 		HTTPServer: GET and POST
 		Serial  SignOn Message 115200kBaud 
 		EEProm support, Toggle P0.5 Pin
 		PageData starts at 0x30000
 Copyright Digital Shortcut 2008 **/

#include	<stdarg.h>
#include	<stdlib.h>
#include	<string.h>

#include	"utils/console.h"
#include	"utils/util.h"

#include	"ARM2148/lpc21xx.h"
#include	"ARM2148/processor.h"
#include	"ARM2148/timerC.h"          	

#include	"types.h"
#include	"Wiznet/w5300.h"
#include	"DigiShort/ds5300.h"
#include	"Wiznet/socket.h"
#include	"http/http_conf.h"
#include	"i2c/i2c.h"


extern	void http_serv(void);

#define HT	9
#define LF	10
#define CR	13

#define BAUD_RATE	115200

#define testR	0x21a


unsigned int	Event, u1;
int		CRdyMax, SpurIntCnt;
int		tcnt, W53ErFlg, sCRcnt, Tst1Flag;
uint32 LogTim0, VoltVal;

extern	int			CmdDone;
extern	int			cSoc;
extern	int 		httpPort;
extern	int			ssrErr[];
extern	uint8 	outBuf[];
extern	uint8		voltBuf[];

extern	void 		Init2148(void);
extern	void 		http_serv_machine(void);
extern	void		CheckCmd(void);
extern	void		LogInit(void);

extern	int 		printf(const char *format, ...);

//  Forward prototypes
void 	P0Init(void);
void 	SpurInit(void);
void 	ToggleP0_7(void);
void 	ToggleP0_5(void);
void 	WizCheck0(void);
void 	ShowIPs(void);
void 	WizNetInit(void);
void 	PrepVars(void);
void	SetMAC(void);
void	LoadEE_MAC(void);
void	UpdateVoltage(void);

char	RevDate[] = {"7/28/2009"};


void P0Init(void)
{
  // Initialize Port0 P0.0-P0.23, P0.25, P0.28-P0.31
  PINSEL0 = (PINSEL0 & ~0x0000000F) | 0x00000005;	/* Enable RxD0 and TxD0              */

  PINSEL0   &= 0x0010FFFF;		// P0.7 .. P0.0 GPIOs
  FIO0DIR   |= 0x0FF03FFF;		// P0.7 .. P0.0 & P0.12..P0.13 Output
  FIO0SET    = 0x0FF13FF1;		// "1" on P0.0 P0.4-P0. & P0.12-P0.13
  
  FIO0CLR = 0x00000100;    			//P0.8 Low
}    


void SpuriousInt(void) __attribute__((naked));
void SpuriousInt(void)
{
	//uint32 v;
	
	ISR_ENTRY();
	
	//v = VICIRQStatus;

	SpurIntCnt++;
	
	VICVectAddr = 0x00000000;             // clear this interrupt from the VIC
	
	ISR_EXIT();                           // recover registers and return
}


void SpurInit(void)
{
  SpurIntCnt = 0;
  
	VICDefVectAddr = (unsigned int)SpuriousInt;
}


void ToggleP0_7(void)
{
	if ( FIO0PIN & 0x00000080 ) 
		FIO0CLR = 0x00000080;    			//P0.7 OFF 
	else 	FIO0SET = 0x00000080;			//P0.7 ON
}

void ToggleP0_5(void)
{
	delay(2000);
	if ( FIO0PIN & 0x00000020 ) 
		FIO0CLR = 0x00000020;    			//P0.5 OFF 
	else 	FIO0SET = 0x00000020;			//P0.5 ON
}

void WizCheck0(void)
{ 
	uint16 v1, v2, v3, v4, v5;
	
	v1 = getMR();							// expected value is 0x3800
  v2 = IINCHIP_READ(RTR);			// expected value is 0x07D0
  v3 = IINCHIP_READ(RCR);			// expected value is 0x..08
  v4 = IINCHIP_READ(IDR);

  v5 = IINCHIP_READ(testR);
  
  printf("MR=%04x RTR=%04x RCR=%02x IDR=%04x M_%x=%04x",
       v1, v2, (v3&0xff), v4, testR, v5);

	if ( (v1==1)&&(v2==0x7d0)&&((v3&0xff)==8)&&(v4==0x5300)&&(v5==0x1234) ) 
		printf("  ** OK **\n\r");
	else
		printf("  ** ???? **\n\r");
       
}  

void ShowIPs(void)
{ 
	uint8	tBuf[10];
	
  Rd5300_bl(SIPR0, &tBuf[0], 4);
  printf("IP:   %d.%d.%d.%d\n\r",tBuf[0],tBuf[1],tBuf[2],tBuf[3]);
  Rd5300_bl(GAR0, &tBuf[0], 4);
  printf("GAR:  %d.%d.%d.%d\n\r",tBuf[0],tBuf[1],tBuf[2],tBuf[3]);
  Rd5300_bl(SUBR0, &tBuf[0], 4);												 // get subnet mask address   
  printf("SUBR: %d.%d.%d.%d\n\r",tBuf[0],tBuf[1],tBuf[2],tBuf[3]);
  Rd5300_bl(SHAR0, &tBuf[0], 6);
  printf("SHAR: %02x:%02x:%02x:%02x:%02x:%02x\n\r",tBuf[0],tBuf[1],tBuf[2],tBuf[3],tBuf[4],tBuf[5]);
  printf("HttpPort: %d", httpPort);
}

uint8 ip_0[4] = {192,168,0,41};                  	// for setting SIP register
uint8 gw[4] = {192,168,0,1};                     	// for setting GAR register 
uint8 sn[4] = {255,255,255,0};                    // for setting SUBR register
uint8 zero_1[20];
uint8 mac_1[6] = {0x00,0x08,0xDC,0x00,111,200};   // WizNet Mac Address
uint8 mac_0[6] = {0x06,0x44,0x53,1,1,2};    			// Locally Administered Mac Addr + SN_112
uint8 zero_2[20];

uint8 tx_mem_conf[8] = { 8, 8, 8, 8, 8, 8, 8, 8};  				// for setting TMSR, all socket TxBufs-14k 
uint8 rx_mem_conf[8] = { 8, 8, 8, 8, 8, 8, 8, 8};         // for setting RMSR, all socket RxBufs-2k  

	// Initialize W5300 for Ethernet Operations
void	WizNetInit(void)
{

  /* initiate W5300 */
  iinchip_init();			// MR_RES & MR_IND
  W5300Init2();				// Init interrupts for 5300
  
  // configure internal W5300 TX/RX Memory Buffers
  
  if( sysinit(tx_mem_conf, rx_mem_conf)==0 ) {
    printf("MEMORY CONFIG ERR.\r\n\r");
    while(1);
  }
  
  IINCHIP_WRITE(testR, 0x1234);
  
  SetMAC();
 
}

void	SetMAC(void)
{
	uint8 tb[0x32];

  eepromRead(0, tb, 0x30);
  
  if ( (tb[0] == 0xff) && (tb[1] == 0xff)	&& (tb[2] == 0xff) ) {
	  setSIPR(ip_0);              // set source IP address
  	setGAR(gw);                	// set gateway IP address
  	setSUBR(sn);               	// set subnet mask address
  	setSHAR(mac_0); 						// set source hardware address
  	httpPort = HTTP_PORT;

  } else	{
  	LoadEE_MAC();
	}
}
  	

void	LoadEE_MAC(void)
{
	uint8 tc[36];
	
	eepromRead(0, tc, 0x22);
	delay(100000);
	
	setSHAR(&tc[0x00]); 					// set source hardware address MAC
	setSIPR(&tc[0x08]);          	// set source IP address
 	setGAR(&tc[0x10]);            // set gateway IP address
 	setSUBR(&tc[0x18]);           // set subnet mask address
	
	httpPort = tc[0x20] + 256*tc[0x21];
}	

void	PrepVars(void)
{
	
	W53ErFlg = 0;
	sCRcnt = 0;
	
}

// Pseudo Voltmeter
void	UpdateVoltage(void)
{
	int v;
	char tb[10];
	
	VoltVal += 27;
	v = 200+(VoltVal%120); // miliVolts in range 200-319
	
	itoa(v, tb, 10);
	memcpy ( (char*)&voltBuf[2], &tb[3], 3);
}
	

	int
main (void)
{
	PrepVars();
		
	Init2148();			//LPC2148 PLL, CLK, PORTs startup init
	
	P0Init();
	P1Init();
	SpurInit();
	
	// init console Baud Rate 115000kbd
	ConsoleInit(60000000 / (16 * BAUD_RATE));
	printf("\n\r#####====  HTTP Server_Demo %s  ====#######\n\r", RevDate );

	timerInit();
	LogInit();
	i2cInit();
	
	W5300PwrOn();
	WizNetInit();
  
	enableIRQ();

	WizCheck0();
  ShowIPs();
  
  CmdDone = 1;
  Tst1Flag = 1;
  Event = 0;
  cSoc = 0;
  
	for (;;) {
		CheckCmd();
		//ToggleP0_5();
		//UpdateVoltage();
		http_serv_machine();
	}
	
  return (0);
}
