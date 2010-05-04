/** @file
 * Command Interpreter
 */
/* copyright ©2008, 2008 #001142 */

#include <stdlib.h>
#include <string.h>

#include	"console.h"

#include	"../ARM2148/lpc21xx.h"
#include	"../ARM2148/processor.h"

#include	"types.h"
#include	"../Wiznet/w5300.h"
#include	"../utils/util.h"
#include	"../i2c/i2c.h"

int			CmdLen, CmdRest, CmdDone;
char		CmdStr[30], cmd, scmd;
char*		CmdPtr;

extern	unsigned int	SrvCnt, StarCnt, ir_t1;
extern	uint32 miliSec, LogTim0;
extern	int SpurIntCnt, CRdyMax;
extern	uint8 	outBuf[];
extern	uint8 	inBuf[];
extern	uint8		tmpBuf[];	
extern	char		RevDate[];	


extern	void WizCheck0(void);
extern	void ShowIPs(void);
extern	void ShowSSRs(void);

void	CheckCmd(void);
void	LogInit(void);
void	LogWr( uint16 data );
void	LogWrTim( void );
void	LogDisplay( void );
int 	printf(const char *format, ...);
int 	scanDecNumber( char* StrBuf, int maxLen, int* number);
int		RdUi8Seq( char* StBuf, int Len,  uint8* numBuf );
int		InitEE_IP(void);
void	DumpEE(uint16 addr, int len);
void 	ClearEE(void);

#define HT	9
#define LF	10
#define CR	13
#define ESC	27

#define LOGMAX	1200

int 	tmp, LogCnt;
uint16	LogData[LOGMAX+5];

int	Get4cDecNum(char* nStr);
int	GetCmdLine(void);

extern	uint8		ip_0[];

static unsigned char ip_a[4];                   // alternate setting SIP
static unsigned char sn_a[4];                   // alternate setting SUBR 
static unsigned char gar_a[6];                  // alternate setting GAT
static unsigned char mac_a[6];                  // alternate setting MAC


void	CheckCmd(void)
{
	uint8 	tb[30];
	int len = 0;
	int v1;
	int i;

	if ( CmdDone ) {
		CmdDone = 0;
		printf("\n\r!");
	}
	
	if ( GetCmdLine()&&(CmdLen>0) ) {
		CmdDone = 1;
		cmd = CmdStr[0];
     if ( (cmd>0x60)&&(cmd<0x7B) ) {
			cmd = cmd - 0x20;		// ASCII toupper
		}
		CmdRest--;
			      
    switch (cmd) {
		case 'L':
			LogDisplay();
			break;

		case 'I':
			// INFO
			printf( "### HTTP Server_Demo %s ###\n\r", RevDate);
			printf( "EEPROM:\n\r");
			DumpEE(0, 0x30); printf( "\n\r" );
			
			ShowIPs();
			break;

		case 'F': {
			char MStr[] = {"BrownAB Fox123 jumpsABC 1234\r\n\r\n"};
			char CStr[] = {"\r\n"};
			printf("\n\r%02X %02X", CStr[0], CStr[1]);
			findstr(&MStr[0], "Fox");
			findstr(&MStr[0], "123");
			findstr(&MStr[0], "1234");
			findstr(&MStr[0], "Br");
			findstr(&MStr[0], "j");
			findstr(&MStr[0], "XYZ");
			findstr(&MStr[0], "\r\n\r\n");
			break;
		}
			
		case 'H':
			// Help
			printf( "Commands:"); 
			printf( "\n\r L  - LogDisplay");
			printf( "\n\r I  - Info");
			printf( "\n\r EC - Clear EE");
			printf( "\n\r ED - Dump EE");
			printf( "\n\r EL - Load/Init EE_IPs");
			printf( "\n\r EI - set EE_IP");
			printf( "\n\r EM - set EE_MAC");
			printf( "\n\r ES - set EE_SN");
			printf( "\n\r EG - set EE_GAR");
			printf( "\n\r EP - set EE_Port");
			break;

		case 'E':
			// EEPROM commands
			if (CmdStr[1] == 0) {
				printf("\n\r????");
			} else {
				i = 1;
	   		while ( CmdStr[i] != 0 ) {
					scmd = CmdStr[i];
					if ( (scmd>0x60)&&(scmd<0x7B) ) {
						scmd = scmd - 0x20;		// ASCII toupper
					}
					i++;

					switch (scmd) {
						case 'D' :
							// Dump EE
							DumpEE(0, 0x60);
							break;
						
						case 'C' :
							// Clear EE
							ClearEE();
							break;
						
						case 'L' :
							// Load - Initialize IP, MAC, GAR, SN, Port
							InitEE_IP();
							delay(100000);
							DumpEE(0, 0x60);
							break;
						
						case 'I' :
							// Set Source IP Address - SIPR 
						  len = RdUi8Seq( &CmdStr[i], 4, ip_a );
						  if ( len > 0 ) {
							  printf("IP: %d.%d.%d.%d", ip_a[0], ip_a[1], ip_a[2], ip_a[3]);
							  setSIPR(ip_a);
								memcpy ( &tb[2], ip_a, 4 );
								if ( eepromWrite(8, tb, 4) != 0 ) printf("\n\rWrEE Err");
						  }
						  else printf("????\n\r");
						  break;
						  
						case 'G' :
							// Set Source Gateway Address - GAR 
						  len = RdUi8Seq( &CmdStr[i], 4, gar_a );
						  if ( len > 0 ) {
							  printf("GAR: %d.%d.%d.%d", gar_a[0], gar_a[1], gar_a[2], gar_a[3]);
							  setGAR(gar_a);
								memcpy ( &tb[2], gar_a, 4 );
								if ( eepromWrite(0x10, tb, 4) != 0 ) printf("\n\rWrEE Err");
						  }
						  else printf("\n\r????");
						  break;
						  
						case 'S' :
							// Set Subnet Mask Address - SUBR
						  len = RdUi8Seq( &CmdStr[i], 4, sn_a );
						  if ( len > 0 ) {
						  	printf("SN: %d.%d.%d.%d", sn_a[0], sn_a[1], sn_a[2], sn_a[3]);
						  	setSUBR(sn_a); 
								memcpy ( &tb[2], &sn_a[0], 4 );
								if ( eepromWrite(0x18, tb, 4) != 0 ) printf("\n\rWrEE Err");
					  	}
						  else printf("\n\r????");
						  break;
						  
						case 'M' :
							// Set MAC Address
						  len = RdUi8Seq( &CmdStr[i], 6, mac_a );
						  if ( len > 0 ) {
						  	printf("MAC: %02x:%02x:%02x:%02x:%02x:%02x", 
						  	mac_a[0], mac_a[1], mac_a[2], mac_a[3], mac_a[4], mac_a[5]);
						  	setSHAR(mac_a);
						  	memcpy ( &tb[2], &mac_a[0], 6 );
						  	if ( eepromWrite(0, tb, 6) != 0 ) printf("\n\rWrEE Err"); 
					  	}
						  else printf("\n\r????");
						  break;
						  
						case 'P' :
							// Set HTTP Port
							scanDecNumber( &CmdStr[i], 5, &v1); 
						  printf("New htPort = %d", v1);
							memcpy ( &tb[2], &v1, 2 );
							if ( eepromWrite(0x20, tb, 2 ) != 0 ) printf("\n\rWrEE Err");
						  break;

						default: break;

					}
					i += len;
				}
			}
		break;
			
		default:
			printf("*CmdErr\n\r");
			break;
		}
		CmdLen = 0;
	}					
}												

int	GetCmdLine(void)
{
	int CRdy;
	int c;

	CRdy = 0;
	c = my_getchar();
	if ( c != EOF ) {
		// show on console
		// putchar(c);
		printf("%c", c);
		if ( c == CR ) {
			CmdStr[CmdLen]=0;
			CRdy = 1;
		} else {
			CmdStr[CmdLen] = c;
			CmdLen++;
		}
	}
	CmdRest = CmdLen;
	return CRdy;
}

	// Get 4character Decimal Number
int	Get4cDecNum(char* nStr)
{
	int i, num, v;
	char ch;
	
	num = 0;
	// Skip blank spaces at the beginning
	for (i = 0; i < 3; i++) {
		ch = *nStr;
		if ( ( ch == ' ')||(ch == HT) ) {
			nStr++;
			CmdRest--;
		} else break;
	}	
		
	for (i = 0; i < 4; i++) {
		ch = *nStr;
		nStr++;
		CmdRest--;
		if ( ( ch == ' ')||(ch == HT) ) break;
		v = 0;
		if ( (ch>0x2f)&&(ch<0x3a) ) {
			v = ch-0x30;
		} 
		num = (num*10)+v;
		
		if ( CmdRest==0 ) break;
	}
	CmdPtr = nStr;	
	return num;
}		


//--scan string and extract decimal number
int scanDecNumber( char* StrBuf, int maxLen, int* number)
{
	int i   = 0;
	*number = 0;
	while ( (StrBuf[i] == ' ')||(StrBuf[i] == '.') ) { i++; maxLen++; }
	while ((StrBuf[i] >= '0') && (StrBuf[i] <= '9') && (i < maxLen)) {
		*number  *= 10;
		*number  += (StrBuf[i] & 0x0000000F);
		i++;
	}
	return i;
}


int	RdUi8Seq( char* StBuf, int Len,  uint8* numBuf )
{
	int j = 0;
	int ll, v;
	uint8 OKFlag = 0;
	uint8	tbuf[10];
	char* ibufp;
	
	ll = 0;
	ibufp = StBuf;
	for ( j=0; j<Len; j++ ) {
		ll = scanDecNumber( ibufp, 3, &v);
		if (ll == 0) { 
			OKFlag = 0; 
			break; 
		}
		tbuf[j] = (uint8)(v&0xff);
		ibufp += ll;
		OKFlag = 1;
	}
	if ( OKFlag == 0 ) return 0;
	 
	for ( j=0; j<Len; j++ ) numBuf[j] = tbuf[j];
	
	return ll;
}

/***********
EEPROM MAC_IP Store Record
	MAC - 6bytes addr: 0x00-0x05
	IP  - 4bytes addr: 0x08-0x0b
	GAR - 4bytes addr: 0x10-0x13
	SN  - 4bytes addr: 0x18-0x1b
	Port- 2bytes addr: 0x20-0x21
***********/
int InitEE_IP(void)
{
	uint8 	mac_ee[] = {0x06,0x44,0x53,0x01,0x01,0x02,0,0};      
	uint8 	ip_ee[] = {192,168,0,41,0,0,0,0};
	uint8 	gar_ee[] = {192,168,0,1,0,0,0,0};
	uint8 	sn_ee[] = {255,255,255,1,0,0,0,0};
	uint8		port_ee[] = {80,0};
	
	memcpy ( &outBuf[(0x00+2)], mac_ee, 8 );
	memcpy ( &outBuf[(0x08+2)], ip_ee, 8 );
	memcpy ( &outBuf[(0x10+2)], gar_ee, 8 );
	memcpy ( &outBuf[(0x18+2)], sn_ee, 8 );
	memcpy ( &outBuf[(0x20+2)], port_ee, 2 );
	if ( eepromWrite(0, outBuf, 0x22) != 0 ) {
		printf("\n\rInitEE Err1");
		return -1;	//error
	}
	
	return 0;
	
}

void DumpEE(uint16 addr, int len)
{	
	int r, i, idx, sLen;
	sLen = len;	
	
	r = eepromRead(addr, outBuf, len);
	
	idx = 0;
	while ( idx < sLen ) {
		printf("%03d  ", (addr+idx) );
		for (i=0; i<16; i++) printf("%02x ", outBuf[idx+i]);
		printf("  ");
		for (i=0; i<16; i++) printf("%c", outBuf[idx+i]);
		idx += 16;
		if (idx<sLen) printf("\n\r");
	}
}	


void ClearEE(void)
{
	int		i;
	uint16 addr;
	
	addr = 0;
	memset ( &outBuf[2], 0xff, 64 );
	for (i=0; i<6; i++ )	{	// i<<128
		eepromWrite( addr, outBuf, 64 );
		delay(100000);
		addr += 64;
	}
}

	
void	LogInit(void)
{
	int i;
	
	for (i=0; i<LOGMAX; i++ ) {
		LogData[i] = 0x1111;
	}
	
	LogCnt = 0;
}


void	LogWr( uint16 data )
{
	if ( LogCnt == 0 ) LogTim0 = miliSec;
	
	if ( LogCnt < LOGMAX ) {
		LogData[LogCnt] = data;
		LogCnt++;
	}
}

void	LogWrTim( void )
{
	if ( LogCnt < LOGMAX ) {
		uint16 td;
		td = ((miliSec-LogTim0)&0x3fff)|0xc000;
		LogData[LogCnt] = td;
		LogCnt++;
	}
}

uint16 LogRMark[] = { 0x11, 0x20, 0x21, 0x22, 0x23, 
											0x24, 0x25, 0x26, 0x27, 0x28, 0x29,
											0x31, 0x32, 0x33, 0x35,
											0x41, 0x42, 0x45, 0x47, 0x48, 0x49,
											0x50, 0x51, 0x56,
											0x70, 0x71, 0x77, 0x78, 0x88,
										 	0x551, 0x555,
										 	0x771, 0x772, 0x773, 0x774,
										 	0 };
										  
int	LogRLen[] = { 3, 3, 3, 3, 3,
									3, 3, 3, 3, 4, 4,
									4, 5, 4, 3,
									3, 4, 3, 3, 3, 2,
									3, 3, 2,
									3, 3, 3, 5, 3,
									6, 3,
									5, 1, 1, 5 };
										 
void LogDisplay( void )
{
	int i, j, cnt, c1, l;
	uint16 v0, v1;
	
	printf ( "\n\rLogCnt= %d Tim=%d.%d ", LogCnt, (int)(miliSec/1000),(int)(miliSec%1000) );
	if ( LogCnt == 0 ) {
		return;
	}

	cnt = LogCnt;
	j = 0;
	l = 1;

	if ( CmdRest==0 ) {
		while ( cnt > 0 ) {
			printf("\n\r");
			for ( i=0; i<10; i++ ) {
				printf("%04x ", LogData[j]);
				j++;
				cnt--;
				if ( cnt==0 ) break;
			}
		}
	} else {
		while ( cnt > 0 ) {
			v0 = LogData[j++];
			printf("\n\r%3d   %04x  ", l++, v0);
			i = 0;	
			while ( (LogRMark[i] > 0) && (LogRMark[i] != v0) ) i++;
			if ( LogRMark[i]==0 ) c1 = 1; else c1 = LogRLen[i];
			if ( c1 > 1 )	{
				for ( i=1; i<(c1-1); i++ ) printf( "%04x ", LogData[j++] );
				v1 = LogData[j++];
				// TimeDelta Marker ?
				if ( (v0<0x75) && ((v1&0xC000)==0xC000) ) {	
					v1 = v1&0x3FFF;
					for ( i=0; i<(4-c1); i++ ) printf("     ");
					printf( " dt= %d", v1 );
				}
				else printf( "%04x ", v1 );
			}
			cnt = cnt - c1;
		}
	}
	LogInit();
}

