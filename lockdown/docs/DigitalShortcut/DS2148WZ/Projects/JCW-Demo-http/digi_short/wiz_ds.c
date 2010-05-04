/** file wiz_ds.c
 * WIZnet-Digital Shortcut stuff	
 * Miscelaneous functions for DS2148WZ Http Server
 * Rev 1.0 JD 3-10-2009
 * Copyright Digital Shortcut Inc. (BSD licence) 2009 **/

#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#include <stdio.h>

#include <inttypes.h>

#include "FreeRTOS.h"
#include "task.h"

#include "../wiz5300/ds5300.h"
#include "../wiz5300/w5300.h"

#include "wiz_ds.h"


#define testR	0x21a
#define LOGMAX	400

int 	r, LogCnt;
uint16	LogData[LOGMAX+5];


int 	SCnt, W53IntCnt, SpurIntCnt, CRdyMax;	
int		tcnt, W53ErFlg, sCRcnt;
uint32	LogTim0;

extern	uint8		SpurInt[];
extern 	int			ssrErr[];


extern	void SpuriousW5300Int(void) __attribute__((naked));


void WizCheck0(void)
{ 
	uint16 w1, w2, w3, w4, w5;
	
	w1 = getMR();							// expected value is 0x0001
  w2 = IINCHIP_READ(RTR);			// expected value is 0x07D0
  w3 = IINCHIP_READ(RCR);			// expected value is 0x..08
  w4 = IINCHIP_READ(IDR);

  w5 = IINCHIP_READ(testR);
  
  printf("MR=%04x RTR=%04x RCR=%02x IDR=%04x M_%x=%04x",
       w1, w2, (w3&0xff), w4, testR, w5);
	if ( (w1==1)&&(w2==0x7d0)&&((w3&0xff)==8)&&(w4==0x5300)&&(w5==0x1234) ) 
		printf("  **OK\n");
	else
		printf("  ** ???? **\n");

}  

void ShowIPs(void)
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

void ShowSSRs(void)
{
	int i;
	
	printf("\nSocket SSR: ");
	for (i = 0; i < MAX_SOCK_NUM; i++) printf("%02x  ", getSn_SSR(i));

	printf("\nSocket IMR: ");
	for (i = 0; i < MAX_SOCK_NUM; i++) printf("%02x  ", getSn_IMR(i));
	
	printf("\nSpurInt:    ");
	for (i = 0; i < MAX_SOCK_NUM; i++) printf("%02x  ", SpurInt[i]);
	
	printf("\n");
}

void W5300PwrOn(void)
{
  GPIO1_FIOPIN  = WIZ_ON|WIZ_RD|WIZ_WR|WIZ_RES;		// WizOn=1, LATCH=0, CS=0, Rd=1, Wr=1, /RES=1
  delay(200000);
  
  // Activate WIZ_RESET
	GPIO1_FIOCLR  = WIZ_RES;	  
  delay(50);
	GPIO1_FIOSET  = WIZ_RES;	  
  delay(200000);
}

void W5300PwrOff(void)
{
	// Set all W5300 signals at "0"
  GPIO1_FIOCLR3 = LATCH_STRBb;			// Latch Transparent
  delay(100);
  GPIO1_FIOCLR  = WIZ_A0|WIZ_A1|WIZ_A2|WIZ_RD|WIZ_WR|WIZ_RES;
  delay(100);
  GPIO1_FIOSET3 = WIZ_CSb;
  delay(100);
  
	GPIO1_FIOCLR  = WIZ_ON;		// WizOn=0
  delay(100);
}

void W5300IntInit(void)
{
	int i;
	
  SpurIntCnt = 0;
  CRdyMax = 0;
  
	VIC_DefVectAddr = (unsigned int)SpuriousW5300Int;

	for (i = 0; i < MAX_SOCK_NUM; i++) {
		// Enable	only SENDOK & TIMEOUT Ints
		setSn_IMR(i, 0x10); 
				
		ssrErr[i] = 0;
	}
}


uint8 ip[4] = {192,168,0,41};                   	// for setting SIP register
uint8 gw[4] = {192,168,0,1};                     	// for setting GAR register 
uint8 sn[4] = {255,255,255,0};                    // for setting SUBR register
uint8 mac_0[6] = {0x06,0x44,0x53,1,1,2};      		// for setting SHAR register

uint8 tx_mem_conf[8] = {8,8,8,8,8,8,8,8};          // for setting TMSR 
uint8 rx_mem_conf[8] = {8,8,8,8,8,8,8,8};          // for setting RMSR 

	// Initialize W5300 for Ethernet Operations
void	WizNetInit(void)
{
  /* initiate W5300 */
  iinchip_init();			// MR_RES & MR_IND
  W5300IntInit();			// Init interrupts for 5300
  
  // configure internal W5300 TX/RX Memory Buffers
  if( sysinit(tx_mem_conf, rx_mem_conf)==0 ) {
    //printf("MEMORY CONFIG ERR.\r\n");
    while(1);
  }
  
  IINCHIP_WRITE(testR, 0x1234);

  setSIPR(ip);               	// set source IP address
  setGAR(gw);                	// set gateway IP address
  setSUBR(sn);               	// set subnet mask address
  setSHAR(mac_0); 							// set source hardware address	

  setIMR(0xFF);
}


void	w5300Init(void)
{	
  GPIO1_FIODIR |= 0x03FF0000;				// P1.16 .. P1.25 Output
  GPIO1_FIOPIN  = WIZ_ON|WIZ_RD|WIZ_WR|WIZ_RES;		// WizOn=1, LATCH=0, CS=0, Rd=1, Wr=1, /RES=1
	
	W5300PwrOn();
	
	WizNetInit();
	
}


void delay(unsigned long d)
{
	for(; d; --d)
	{
		asm volatile ("nop");
	}
}

void	LogIni(void)
{
	int i;
	
	for (i=0; i<LOGMAX; i++ ) {
		LogData[i] = 0x1111;
	}
	
	LogCnt = 0;
}

void	LogWr( uint16 data )
{
	if ( LogCnt == 0 ) LogTim0 = xTaskGetTickCount();
	
	if ( LogCnt < LOGMAX ) {
		LogData[LogCnt] = data;
		LogCnt++;
	}
}

void	LogWrTim( void )
{
	if ( LogCnt < LOGMAX ) {
		uint16 td;
		//td = ((miliSec-LogTim0)&0x1fff)|0xc000;
		td = ((xTaskGetTickCount()-LogTim0)&0x1fff)|0xc000;
		LogData[LogCnt] = td;
		LogCnt++;
	}
}

uint16 LogRMark[] = { 0x11, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x28,
											0x31, 0x32, 0x33, 
											0x41, 0x42, 0x45, 0x47, 0x48, 0x49,
											0x50, 0x51,
										 	0x551, 0x555,
										 	0x771, 0x772, 0x773, 0x774,
										 	0 };
										  
int	LogRLen[] = { 3, 3, 3, 3, 3, 3, 3, 2,
									4, 5, 4,
									3, 4, 3, 2, 3, 2,
									3, 3,
									6, 3,
									5, 1, 1, 5 };
										 
void LogDisplay( void )
{
	int i, j, cnt, c1, l;
	uint16 w1;
	
	printf ( "LogCnt= %d \n", LogCnt );
	if ( LogCnt == 0 ) {
		return;
	}

	cnt = LogCnt;
	j = 0;
	l = 1;

//	if ( CmdRest==0 ) {
	if ( 0 ) {
		while ( cnt > 0 ) {
			printf("\n");
			for ( i=0; i<10; i++ ) {
				printf("%04x ", LogData[j]);
				j++;
				cnt--;
				if ( cnt==0 ) break;
			}
		}
	} else {
		while ( cnt > 0 ) {
			w1 = LogData[j++];
			printf("\n%3d   %04x  ", l++, w1);
			i = 0;	
			while ( (LogRMark[i] > 0) && (LogRMark[i] != w1) ) i++;
			if ( LogRMark[i]==0 ) c1 = 1; else c1 = LogRLen[i];
			for ( i=1; i<(c1-1); i++ ) printf( "%04x ", LogData[j++] );
			w1 = LogData[j++];
			// TimeDelta Marker ?
			if ( (w1&0xC000)==0xC000 ) {
				w1 = w1&0x1FFF;
				for ( i=0; i<(4-c1); i++ ) printf("     ");
				printf( " dt= %d", w1 );
			}
			else printf( "%04x ", w1 );
			cnt = cnt - c1;
		}
		printf("\n");
	}
	LogIni();
}

char* itoa(unsigned int num, char* buf, int radix )
{
	char *p;
	buf[0]=buf[1]=buf[2]=buf[3]=buf[4]=buf[5]='0';
	buf[6] = '\0';		

	if ( num > 0 ) {
		p = &buf[5];
		while (num != 0) {
			*p-- = "0123456789abcdef"[num % radix];
			num /= radix;
		}
	}
	p = &buf[0];
	return p;
}
  
