/** file httpserv.c
 * Http Server as a Task
 * webSiteData at 0x30000, begining with site_files_table(offset, size, type)
 *
 * Rev 1.0 JD 3-10-2009
 * Copyright Digital Shortcut Inc. (BSD licence) 2009 **/

#include <stdint.h>	// uint8_t 
#include <string.h>
#include <stdio.h>

#include	"FreeRTOS.h"
#include	"task.h"

#include	"../wiz5300/types.h"
#include	"../wiz5300/w5300.h"
#include	"../wiz5300/ds5300.h"
#include	"../wiz5300/socket.h"
#include	"wiz_ds.h"
#include	"httpserv.h"
#include	"PageData.h"
#include	"http_conf.h"


extern char* 		itoa(unsigned int num, char* buf, int radix );
extern	void		LogWr( uint16 data );
extern	void		LogWrTim( void );

int	send_DS(SOCKET s, uint8 * buf, int len);
int	send1st_DS(SOCKET s, uint8 * buf, int len);
int	wait4sendDone(SOCKET s);	
int	hex2int(char ch);
int PrepHeader(int pLen, char pType);
uint8 ToUpper(uint8 ch);
int	CheckRequest(int len);
void socket_return(void);
int	hex2int(char ch);

static	int			cSoc, txfree_size;


#define CR	13		// 0x0D
#define LF	10		// 0x0A


struct p_rec *p_ptr;


#define	OBUF_SIZE		512
#define	IBUF_SIZE		512

		
uint8 outBuf[OBUF_SIZE+1];
uint8 inBuf[IBUF_SIZE+1];

static	uint8	SockStat[MAX_SOCK_NUM];

// Connection Established Phase:
static	uint8	EstbPhase[MAX_SOCK_NUM];

#define ESTB_NONE			0
#define ESTB_RCVD			1
#define ESTB_TRX			2
#define ESTB_TXNRDY		3


static	uint16 fileIdx[MAX_SOCK_NUM];

uint8	phpBuf[64] = {"2.345     "};

char* SndBPtr[MAX_SOCK_NUM];
int		SndLen[MAX_SOCK_NUM];	
int		wait_cnt[MAX_SOCK_NUM];
int		SndTim[MAX_SOCK_NUM];	
	

#define HD_HTTP_OK	"HTTP/1.1 200 OK\r\n"
#define HD_ERR_400	"HTTP/1.1 400 Bad Request\r\n"

#define HD_SRVR_DS	"Server: Digital Shortcut Inc Server\r\n"
#define	HD_ENCGZIP	"Content-Encoding: gzip\r\n"

#define	HD_CONT_TXHTML 	"Content-Type: text/html\r\n"
#define	HD_CONT_GIF 		"Content-Type: image/gif\r\n"
#define	HD_CONT_PNG 		"Content-Type: image/png\r\n"
#define	HD_CONT_JPG 		"Content-Type: image/jpeg\r\n"
#define	HD_CONT_CSS 		"Content-Type: text/css\r\n"
#define	HD_CONT_ICO 		"Content-Type: image/x-icon\r\n"

#define	HD_CONT_LEN 	"Content-Length:  "

#define	HD_DONE	"\r\n"
#define	HD_DONE2	"\r\n\r\n"

//#define HD_DATE		"Date: Mon, 08 Jan 1990 12:45:31 GMT\r\n"

#define	HD_TXT	HD_HTTP_OK HD_SRVR_DS HD_CONT_TXHTML HD_CONT_LEN 
#define	HD_TXHT_GZ	HD_HTTP_OK HD_SRVR_DS HD_CONT_TXHTML HD_ENCGZIP HD_CONT_LEN 
#define	HD_GIF	HD_HTTP_OK HD_SRVR_DS HD_CONT_GIF HD_CONT_LEN  
#define	HD_JPG	HD_HTTP_OK HD_SRVR_DS HD_CONT_JPG HD_CONT_LEN  
#define	HD_PNG	HD_HTTP_OK HD_SRVR_DS HD_CONT_PNG HD_CONT_LEN  
#define	HD_CSS	HD_HTTP_OK HD_SRVR_DS HD_CONT_CSS HD_CONT_LEN
#define	HD_CSS_GZ	HD_HTTP_OK HD_SRVR_DS HD_CONT_CSS HD_ENCGZIP HD_CONT_LEN
#define	HD_PHP	HD_HTTP_OK HD_SRVR_DS HD_CONT_TXHTML HD_CONT_LEN
#define	HD_ICO	HD_HTTP_OK HD_SRVR_DS HD_CONT_ICO HD_CONT_LEN
#define	HD_ICO_GZ	HD_HTTP_OK HD_SRVR_DS HD_CONT_ICO HD_ENCGZIP HD_CONT_LEN

#define	HD_ERRX	HD_ERR_400 HD_SRVR_DS HD_DONE
#define	HD_OKTXT	HD_HTTP_OK HD_SRVR_DS HD_CONT_TXHTML HD_DONE

// File types
#define TEXT_TYPE			1
#define GIF_TYPE			2
#define CSS_TYPE			3
#define JPEG_TYPE			6
#define PNG_TYPE			7
#define HTML_GZ_TYPE	4
#define CSS_GZ_TYPE		5
#define ICON_TYPE			8
#define PHP_TYPE			9

#define PHP_LEN				8



int PrepHeader(int pLen, char pType)
{
	char tBuf[20];
	uint8* poB;
	char* pp;
	int leni, tlen;
	
	// combine header HTTP
	tlen = 0;
	poB = &outBuf[0];
	
  switch (pType) {
	case TEXT_TYPE:
		//page_type 1: PLAIN TEXT
		leni = sizeof(HD_TXT)-1;
		memcpy( poB, HD_TXT, leni );
		break;
		
	case GIF_TYPE:
		//page_type 2: GIF image
		leni = sizeof(HD_GIF)-1;
		memcpy( poB, HD_GIF, leni );
		break;

	case CSS_TYPE:
		//page_type 3: PLAIN CSS
		leni = sizeof(HD_CSS)-1;
		memcpy( poB, HD_CSS, leni );
		break;
				
	case HTML_GZ_TYPE:
		//page_type 4: GZIPed HTML TEXT
		leni = sizeof(HD_TXHT_GZ)-1;
		memcpy( poB, HD_TXHT_GZ, leni );
		break;
		
	case CSS_GZ_TYPE:
		//page_type 5: GZIPed CSS
		leni = sizeof(HD_CSS_GZ)-1;
		memcpy( poB, HD_CSS_GZ, leni );
		break;

	case JPEG_TYPE:
		//page_type 6: JPEG image
		leni = sizeof(HD_JPG)-1;
		memcpy( poB, HD_JPG, leni );
		break;

	case PNG_TYPE:
		//page_type 6: PNG image
		leni = sizeof(HD_PNG)-1;
		memcpy( poB, HD_PNG, leni );
		break;

	case ICON_TYPE:
		//page_type 8: ICO image/x-icon
		leni = sizeof(HD_ICO)-1;
		memcpy( poB, HD_ICO, leni );
		break;

	case PHP_TYPE:
		//page_type 9: PHP
		leni = sizeof(HD_PHP)-1;
		memcpy( poB, HD_PHP, leni );
		break;
		
	default:
		//default page_type 1: PLAIN TEXT
		leni = sizeof(HD_TXT)-1;
		memcpy( poB, HD_TXT, leni );
		break;
	}
				
	tlen += leni;
	poB += leni;
	
	pp = itoa(pLen, &tBuf[0], 10);
	leni = strlen(pp);
	memcpy( poB, pp, leni );
	tlen += leni;
	poB += leni;
	
	leni = sizeof(HD_DONE2)-1;
	memcpy( poB, HD_DONE2, leni );
	tlen += leni;
	
	outBuf[tlen] ='\0';
	
	return tlen;
}
	

uint8 ToUpper(uint8 ch)
{
	if ( (ch>='a')&&(ch<='z') )  ch = ch & (~040);
	return ch;
}

int	CheckRequest(int len)
{
	int i, id;
	char* p;
	char tstr[12];
	
	for ( i = 0; i < len; i++ ) {
		inBuf[i] = ToUpper( inBuf[i] );
	}
	
	//printf("\n\rinBuf - %s", inBuf);
	if ( memcmp(inBuf, "GET ", 4)==0 ) {
		if ( memcmp(&inBuf[4], "/ HTTP", 6)==0 ) {
			return 0;
		}
			
		p = memchr( &inBuf[5], '.', len);
		if ( p == NULL ) return -1;
		
		memcpy (tstr, p-7, 7);
		tstr[7] = '\0';
		//printf("\n\rDOT: %s", tstr);
		
		if ( memcmp(&tstr[2], "INDEX", 5)==0 ) {
			return 0;
		}			
			
		if ( memcmp(&tstr[0], "FAVICON", 7)==0 ) {
			return 1;
		}
		if ( (hex2int(tstr[5])>=0)&&(hex2int(tstr[6])>=0) ) {
			id = (hex2int(tstr[5])*16) + hex2int(tstr[6]);
			if ( id > 85 ) id = -1;
			return id;
		}			
		
		return -1;
	}
	
	printf(" Er ");
	return -1;
}

void socket_return(void)
{
	int sn;
	
	for (sn = 0; sn < MAX_SOCK_NUM; sn++) {	
		if ( getSn_SSR(sn) == SOCK_CLOSED ) {
			socket(sn,  Sn_MR_TCP, HTTP_PORT, 0x00);
			listen(sn);
		}
	}
}


portTASK_FUNCTION (vHttpServTask, pvParameters __attribute__ ((unused)))
{
	uint16 v, ts;
	int icnt, pi, hlen, len_done;
	
	cSoc = 0;
	
	for (;;)  {
		v = getSn_SSR(cSoc);
		SockStat[cSoc] = v;
		switch ( v ) {	// sock status
		case SOCK_CLOSED:
			socket(cSoc,  Sn_MR_TCP, HTTP_PORT, 0x00);
			break;
			
		case SOCK_INIT:
			listen(cSoc);
			break;
			
		case SOCK_LISTEN:
			EstbPhase[cSoc] = ESTB_NONE;
			break;
			
		case SOCK_ESTABLISHED:
			switch (EstbPhase[cSoc]) {
			case ESTB_NONE :
				ts = getSn_RX_RSR(cSoc);
				if ( ts>30 ) {	
					// data available in RecvFIFO
					//LogWr(0x88); LogWr(ts); LogWrTim(); 
								
					EstbPhase[cSoc] = ESTB_RCVD;
					uint16 n = getSn_RX_RSR(cSoc);
					if (n > IBUF_SIZE) n = IBUF_SIZE;
					icnt = recv(cSoc, &inBuf[0], n);
   
					pi = CheckRequest(icnt);
					if ( pi == -1 ) {
						// Request Error
						printf("\n\r *** RequestError *** ");
					
						//send_err400(cSoc);
						send1st_DS( cSoc, (uint8 *)HD_ERRX, (sizeof(HD_ERRX)-1) );
						disconnect(cSoc);
						EstbPhase[cSoc] = ESTB_NONE;
					} 
					else {
						// GET Service
						p_ptr = (struct p_rec*)PAGE_INFO_ADDR;
						//printf("   PHead:%d size-%x, type-%d", pi, (p_ptr+pi)->size, (p_ptr+pi)->type );
						if ( (p_ptr+pi)->type == 0xff ) {
							printf(" ***ERROR*** ");
							//send_err400(cSoc);
							send1st_DS( cSoc, (uint8 *)HD_ERRX, (sizeof(HD_ERRX)-1) );
							disconnect(cSoc);
							EstbPhase[cSoc] = ESTB_NONE; 
							break;
						}

						if ( (p_ptr+pi)->type == PHP_TYPE ) {
							// php Request
							// printf(" ** PHP indx=%d", pi);
							hlen = PrepHeader( PHP_LEN, PHP_TYPE );
							if ( hlen > 0 ) {
								//send file header
								send1st_DS(cSoc, &outBuf[0], hlen);
								EstbPhase[cSoc] = ESTB_TRX;
								SndBPtr[cSoc] = (char*)phpBuf;
								SndLen[cSoc] = PHP_LEN;
							}
							break;
						}
												
						hlen = PrepHeader( (p_ptr+pi)->size, (p_ptr+pi)->type );
						if ( hlen > 0 ) {
							//send file header
							send1st_DS(cSoc, &outBuf[0], hlen);
						
							EstbPhase[cSoc] = ESTB_TRX;
							fileIdx[cSoc] = pi;
							SndBPtr[cSoc] = (char*)((p_ptr+pi)->offset+PAGE_INFO_ADDR);
							SndLen[cSoc] = (p_ptr+pi)->size;
						}
					}
					

				}
				break; //case end EstbPhase = ESTB_NONE
				
			case ESTB_RCVD :
				break;
   
			case ESTB_TRX :
				// send chunk of data body (TXWRMAX-max size)
				len_done = send_DS(cSoc, (uint8 *)SndBPtr[cSoc], SndLen[cSoc]);
				if ( len_done == 0 ) 
					break;
				SndBPtr[cSoc] += len_done;
				SndLen[cSoc] -= len_done;
				if ( wait4sendDone(cSoc) == 0 ) {
					EstbPhase[cSoc] = 3;
					break;
				} 
				if ( SndLen[cSoc] == 0 ) {
					// last chunk was sent
					//LogWr(0x25); LogWr(cSoc); LogWrTim();
		
					setSn_CR(cSoc, Sn_CR_DISCON);     // Disconnect
					EstbPhase[cSoc] = 0;
				}
				socket_return();
				break; //case end EstbPhase = ESTB_TRX
				
			case ESTB_TXNRDY :
				// wait for previous SendOK acknowledge (Int)
				if ( wait4sendDone(cSoc) == 1 ) {
					if ( SndLen[cSoc] == 0 ) {
						// last chunk was sent
						LogWr(0x26); LogWr(cSoc); LogWrTim();
						
						setSn_CR(cSoc, Sn_CR_DISCON);     // Disconnect
						EstbPhase[cSoc] = ESTB_NONE;
   
						socket_return();
						break;
					} else
						EstbPhase[cSoc] = ESTB_TRX;
				}
				break; //case end EstbPhase = ESTB_TXNRDY
				
			default:
				break; //case end EstbPhase = unknown
			}
				
			break; //case end SOCK_ESTABLISHED
							
		case SOCK_CLOSE_WAIT:
			disconnect(cSoc);
			close(cSoc);
			break;
							
		}
		
		cSoc++;
		if ( cSoc >= MAX_SOCK_NUM )
			cSoc = 0;
		
		taskYIELD();
	}
			
}


int	send1st_DS(SOCKET s, uint8 * buf, int len)
{
	//LogWr(0x27); LogWr(s); LogWr((uint16)len); LogWrTim();
			
	wiz_write_buf(s, buf, len);    // copy data

	setSn_TX_WRSR(s, len);   
	setSn_CR(s,Sn_CR_SEND);
	
	return 1;
}


int	send_DS(SOCKET s, uint8 * buf, int len)
{
	int cnt;
		
	txfree_size = (int)getSn_TX_FSR(s);
	if ( txfree_size == 0 ) 
		return 0;
			
	cnt = len;
	if ( cnt > txfree_size )	cnt = txfree_size;
	if ( cnt > TXWRMAX )	cnt = TXWRMAX;

	//LogWr(0x28); LogWr(s); LogWr((uint16)cnt); LogWrTim();
				
	wiz_write_buf(s, buf, cnt);    // copy data
	
	setSn_TX_WRSR(s, cnt);   			

	wait_cnt[s] = 0;
	SndTim[s] = xTaskGetTickCount();
	
	return cnt;
}

//int	wait4sendDone(SOCKET s, int length)	
int	wait4sendDone(SOCKET s)	
{
	uint8 isr;
	
	isr=0;
	// wait previous SEND command completion.
	//if ( !((isr = getSn_IR(s)) & Sn_IR_SENDOK) || ((xTaskGetTickCount()-SndTim[s])==0) ) {
	if ( !((isr = getSn_IR(s)) & Sn_IR_SENDOK) ) {
		wait_cnt[s]++;	
		return 0;
	}
	
	if ( wait_cnt[s]>0 )	{
		LogWr(0x29); LogWr(s); LogWr(wait_cnt[s]); LogWrTim();
	}	
			
	setSn_IR(s, Sn_IR_SENDOK);             // clear Sn_IR_SENDOK	
   
	setSn_CR(s,Sn_CR_SEND);
	
	return 1;
}

//hex to int conversion
int	hex2int(char ch)
{
	if ( (ch>='0')&&(ch<='9') )
		return ch - '0';
		
	if ( (ch>='A')&&(ch<='F') )
		return ch - 'A' + 10;
		
	return -1;
}

