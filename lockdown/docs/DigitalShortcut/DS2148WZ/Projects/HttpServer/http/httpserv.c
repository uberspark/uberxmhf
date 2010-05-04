/** @file
 * http server
 */
/* copyright DS©2008, 2008 */

#include <stdint.h>	// uint8_t 
#include <stdlib.h>
#include <string.h>

#include	"../types.h"
#include	"../Wiznet/w5300.h"
#include	"../DigiShort/ds5300.h"
#include	"../Wiznet/socket.h"

#include	"../ARM2148/lpc21xx.h"
#include	"../utils/util.h"

#include	"PageData.h"
#include	"http_conf.h"

extern	int 	putchar(int ch);
extern	void	UpdateVoltage(void);
extern	void	LogWr(uint16 data);
extern	void	LogWrTim(void);
extern	void	timer1Clear(void);
extern	unsigned int getT1(void);
  

int		send_DS(SOCKET s, uint8 * buf, int len);
int		send1st_DS(SOCKET s, uint8 * buf, int len);
int		wait4sendDone(SOCKET s);	
int 	PrepHeader(int pLen, char pType);
uint8 ToUpper(uint8 ch);
int		CheckRequest(int len);
void 	socket_return(void);
void 	http_serv_machine(void);
void	PrepDwnldData(void);

int		cSoc, txfree_size;
int 	httpPort, Snd0Flag;



#define CR	13		// 0x0D
#define LF	10		// 0x0A


#define  STOP_NOW			printf("\n\r### STOP ###");\
											while (1) ;

struct p_rec *p_ptr;


		
uint8 	outBuf[OBUF_SIZE+1];
uint8 	inBuf[IBUF_SIZE+1];

uint32	tmpBuf[400];

uint8	voltBuf[64] = {"2.345     "};

uint8					EstbPhase[MAX_SOCK_NUM];
uint8 * 			SndBPtr[MAX_SOCK_NUM];
unsigned int	SndLen[MAX_SOCK_NUM];	
uint8					SndType[MAX_SOCK_NUM];	

extern int printf(const char *format, ...);

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

#define	HD_CACHE_CNTRL	"Cache-Control: no-cache, must-revalidate\r\n"

#define	HD_CONT_LEN 	"Content-Length:  "

#define	HD_DONE		"\r\n"
#define	HD_DONE2	"\r\n\r\n"

//#define HD_DATE		"Date: Mon, 08 Jan 1990 12:45:31 GMT\r\n"

#define	HD_TXT	HD_HTTP_OK HD_SRVR_DS HD_CONT_TXHTML HD_CONT_LEN 
#define	HD_TXHT_GZ	HD_HTTP_OK HD_SRVR_DS HD_CONT_TXHTML HD_ENCGZIP HD_CONT_LEN 
#define	HD_GIF	HD_HTTP_OK HD_SRVR_DS HD_CONT_GIF HD_CONT_LEN  
#define	HD_JPG	HD_HTTP_OK HD_SRVR_DS HD_CONT_JPG HD_CONT_LEN  
#define	HD_PNG	HD_HTTP_OK HD_SRVR_DS HD_CONT_PNG HD_CONT_LEN  
#define	HD_CSS	HD_HTTP_OK HD_SRVR_DS HD_CONT_CSS HD_CONT_LEN
#define	HD_CSS_GZ	HD_HTTP_OK HD_SRVR_DS HD_CONT_CSS HD_ENCGZIP HD_CONT_LEN
#define	HD_PHP	HD_HTTP_OK HD_SRVR_DS HD_CACHE_CNTRL HD_CONT_TXHTML HD_CONT_LEN
#define	HD_ICO	HD_HTTP_OK HD_SRVR_DS HD_CONT_ICO HD_CONT_LEN
#define	HD_ICO_GZ	HD_HTTP_OK HD_SRVR_DS HD_CONT_ICO HD_ENCGZIP HD_CONT_LEN

#define	HD_ERRX	HD_ERR_400 HD_SRVR_DS HD_DONE
#define	HD_OKTXT	HD_HTTP_OK HD_SRVR_DS HD_CONT_TXHTML HD_DONE


char uplOKmsg[] = {"The file has been uploaded\r\n\r\n"};

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

// Http Send Task Types
#define STATIC				0
#define VOLTM					1
#define DOWNLOAD			2

#define VOLT_LEN			8

#define ESTB_NONE			0
#define ESTB_RCVD			1
#define ESTB_TRX			2
#define ESTB_TXNRDY		3

#define POST_REQ			0x1000


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
	char c;
	
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
		printf("\n\rDOT: %s", tstr);
		
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
	} // End GET Request
	
	if ( memcmp(inBuf, "POST ", 5)==0 ) {
		//c = inBuf[11];
		//inBuf[11] = 0;
		//printf("\n\rPOST inBuf=%s", inBuf);
		//inBuf[11] = c;
		return POST_REQ;
	}
	
	return -1;
}

void socket_return(void)
{
	int sn;
	
	for (sn = 0; sn < MAX_SOCK_NUM; sn++) {	
		if ( getSn_SSR(sn) == SOCK_CLOSED ) {
			socket(sn,  Sn_MR_TCP, (uint16)httpPort, 0x00);
			listen(sn);
		}
	}
}


void http_serv_machine(void)
{
	uint16 v, ts;
	int idx, icnt, pi, hlen, len_done, snd_typ;
	//char tbuf[10];
	//char* p;
	
	v = getSn_SSR(cSoc);
	switch ( v ) {	// sock status
	case SOCK_CLOSED:
		socket(cSoc,  Sn_MR_TCP, (uint16)httpPort, 0x0020);	// No Delayed ACK Enabled
		break;
		
	case SOCK_INIT:
		//printf( "\n\r***SockInit_%d MR=%04x", cSoc, getSn_MR(cSoc) );	
		listen(cSoc);
		break;
		
	case SOCK_LISTEN:
		EstbPhase[cSoc] = ESTB_NONE;
		break;
		
	case SOCK_ESTABLISHED:	{
		int i, EndFlag;
		unsigned int t;
		switch (EstbPhase[cSoc]) {
		case ESTB_NONE :
			ts = getSn_RX_RSR(cSoc);
			if ( ts>30 ) {
				// data available in RecvFIFO
				uint16 n = getSn_RX_RSR(cSoc);
				if (n > IBUF_SIZE) n = IBUF_SIZE;
				icnt = recv(cSoc, &inBuf[0], n);
				
				pi = CheckRequest(icnt);
				//putchar('&');
				
				switch (pi) {
				case POST_REQ:
					// POST Service
					inBuf[icnt] = 0;
					idx = findstr((char*)inBuf, "\r\n\r\n");
					//printf("\n\r***POST len=%d recl=%d DATA Indx=%d \n\r", icnt, n, idx);
					if ( idx != -1 ) {
						//printf("\n\r**POST DATA: ");
						//for ( i = 0; i < 4; i++ ) printf("%c", inBuf[idx+4+i]);
						//printf("   ");	
						//for ( i = 0; i < 4; i++ ) printf("%02x ", inBuf[idx+4+i]);
						//printf("\n\r**End DATA: ");
						idx = icnt-4;
						//for ( i = 0; i < 4; i++ ) printf("%02x ", inBuf[idx+i]);
						if ( (inBuf[idx] == '-')&&(inBuf[idx+1] == '-')&&(inBuf[idx+2] == '\r')&&(inBuf[idx+3] == '\n') ) {
							hlen = PrepHeader( sizeof(uplOKmsg)-1, TEXT_TYPE );
							//printf("\n\r## Post End hlen=%d uplMsgLen=%d", hlen, (int)sizeof(uplOKmsg));
							if ( hlen > 0 ) {
								send1st_DS(cSoc, &outBuf[0], hlen);			//send file header
								EstbPhase[cSoc] = ESTB_TRX;
								SndType[cSoc] = STATIC;						
								SndBPtr[cSoc] = (uint8 *)(uplOKmsg);
								SndLen[cSoc] = sizeof(uplOKmsg)-1;
								EndFlag = 1;
							}
							break;
						} else {
							timer1Clear();
							EstbPhase[cSoc] = ESTB_RCVD;
							break;
						}
					} else	{
						// POST Error
						printf("\n\r *** POST Error *** ");
				
						//send_err400(cSoc);
						send1st_DS( cSoc, (uint8 *)HD_ERRX, (sizeof(HD_ERRX)-1) );
						disconnect(cSoc);
						EstbPhase[cSoc] = ESTB_NONE; 
						break;
					}
						
					break;

				case -1:
					// Request Error
					printf("\n\r ***** RequestError ***** ");
				
					//send_err400(cSoc);
					send1st_DS( cSoc, (uint8 *)HD_ERRX, (sizeof(HD_ERRX)-1) );
					disconnect(cSoc);
					EstbPhase[cSoc] = ESTB_NONE; 
					break;
				
				default:
					// GET Service
					p_ptr = (struct p_rec*)PAGE_INFO_ADDR;
					printf("   PHead:%d size-%x, type-%d", pi, (p_ptr+pi)->size, (p_ptr+pi)->type );
					if ( (p_ptr+pi)->type == 0xff ) {
						printf(" ***ERROR*** ");
						//send_err400(cSoc);
						send1st_DS( cSoc, (uint8 *)HD_ERRX, (sizeof(HD_ERRX)-1) );
						disconnect(cSoc);
						EstbPhase[cSoc] = ESTB_NONE; 
						break;
					}
					
					if ( (p_ptr+pi)->type == PHP_TYPE ) {	// GET PHP Request
						uint8 *	tp;
						uint8	php_id;
						unsigned int tmpl;
						
						tp = (uint8 *)((p_ptr+pi)->offset+PAGE_INFO_ADDR) + (p_ptr+pi)->size;
						printf("\n\r ** PHP indx=%d id=%02x ", pi, *tp );
						for ( i = 0; i < 5; i++ ) {
							tp++;	printf("%02x ", *tp );
						}
						
						tp = (uint8 *)((p_ptr+pi)->offset+PAGE_INFO_ADDR) + (p_ptr+pi)->size + 4;
						tmpl = (*tp)<<24;	tp++;	tmpl += (*tp)<<16;
						tp -=3;
						tmpl += (*tp)<<8;	tp++;	tmpl += *tp;
						tmpl = (tmpl+1)*2;
						printf(" Length=%08x ", tmpl );
						
						tp = (uint8 *)((p_ptr+pi)->offset+PAGE_INFO_ADDR) + (p_ptr+pi)->size;
						php_id = (int)*tp;
						switch (php_id) {
						case VOLTM :
							//send php header
							send1st_DS(cSoc, (uint8 *)(((p_ptr+pi)->offset)+PAGE_INFO_ADDR+2), (p_ptr+pi)->size-2);	
							
							EstbPhase[cSoc] = ESTB_TRX;
							SndLen[cSoc] = tmpl;
							SndType[cSoc] = php_id;
							break;

						case DOWNLOAD :
							//send php header
							send1st_DS(cSoc, (uint8 *)(((p_ptr+pi)->offset)+PAGE_INFO_ADDR+2), (p_ptr+pi)->size-2);	
							
							EstbPhase[cSoc] = ESTB_TRX;
							SndLen[cSoc] = tmpl;
							SndType[cSoc] = php_id;
							break;
							
						default:
							printf(" ***ERROR*** ");
							//send_err400(cSoc);
							send1st_DS( cSoc, (uint8 *)HD_ERRX, (sizeof(HD_ERRX)-1) );
							disconnect(cSoc);
							EstbPhase[cSoc] = ESTB_NONE; 
							break;
						} // End Switch php_id
						break;
					} // End GET PHP
					
					hlen = PrepHeader( (p_ptr+pi)->size, (p_ptr+pi)->type );
					if ( hlen > 0 ) {
						send1st_DS(cSoc, &outBuf[0], hlen);			//send file header
					
						EstbPhase[cSoc] = ESTB_TRX;
						SndType[cSoc] = STATIC;						
						SndBPtr[cSoc] = (uint8 *)((p_ptr+pi)->offset+PAGE_INFO_ADDR);
						SndLen[cSoc] = (p_ptr+pi)->size;
					}
					break;
				} // End Switch pi
			} // End data available in RecvFIFO
			break;
			
		case ESTB_RCVD :
			ts = getSn_RX_RSR(cSoc);
			EndFlag = 0;
			while ( ts>0 ) {
				// data available in RecvFIFO
				uint16 n = getSn_RX_RSR(cSoc);
				if (n > IBUF_SIZE) n = IBUF_SIZE;
				icnt = recv(cSoc, &inBuf[0], n);
				//LogWr(0x25); LogWr((uint16)icnt); LogWrTim();
				Snd0Flag = 0;
				idx = icnt-4;
				//printf("\n\r**End DATA: ");
				//for ( i = 0; i < 4; i++ ) printf("%02x ", inBuf[idx+i]);
				if ( (inBuf[idx] == '-')&&(inBuf[idx+1] == '-')&&(inBuf[idx+2] == '\r')&&(inBuf[idx+3] == '\n') ) {
					hlen = PrepHeader( sizeof(uplOKmsg)-1, TEXT_TYPE );
					//printf("\n\r## Post End hlen=%d uplMsgLen=%d", hlen, (int)sizeof(uplOKmsg));
					if ( hlen > 0 ) {
						send1st_DS(cSoc, &outBuf[0], hlen);			//send file header
					
						EstbPhase[cSoc] = ESTB_TRX;
						SndType[cSoc] = STATIC;						
						SndBPtr[cSoc] = (uint8 *)(uplOKmsg);
						SndLen[cSoc] = sizeof(uplOKmsg)-1;
						EndFlag = 1;
						break;
					}
				}
				ts = getSn_RX_RSR(cSoc);
			}
			if ( EndFlag > 0 )
				break;
				
			//Recv Empty
			if ( !Snd0Flag )	{
				setSn_TX_WRSR(cSoc, 2);
				IINCHIP_WRITE(Sn_TX_FIFOR(cSoc), 0x2020);
				setSn_CR(cSoc, Sn_CR_SEND);
				//t = getT1();
				//LogWr(0x24); 
				//LogWr( (uint16)((t&0xffff0000)>>16) ); 
				//LogWr( (uint16)(t&0xffff) ); 

				while( !(getSn_IR(cSoc) & Sn_IR_SENDOK) ) ;
				Snd0Flag = 1;
				setSn_IR(cSoc, Sn_IR_SENDOK);             // clear Sn_IR_SENDOK	
			}
			break;

		case ESTB_TRX :
			// send chunk of data body (TXWRMAX-max size)
			snd_typ = SndType[cSoc];
			switch (snd_typ) {
			case STATIC :
				len_done = send_DS(cSoc, (uint8 *)SndBPtr[cSoc], SndLen[cSoc]);
				SndBPtr[cSoc] += len_done;
				break;
				
			case VOLTM :
				UpdateVoltage();
				len_done = send_DS(cSoc, voltBuf, VOLT_LEN);
				break;
				
			case DOWNLOAD :
				PrepDwnldData();
				len_done = send_DS(cSoc, (uint8 *)tmpBuf, SndLen[cSoc]);
				break;
				
			default:
				len_done = 0;
				break;
			}// End Switch snd_typ
								
			if ( len_done == 0 )
				break;
				
			SndLen[cSoc] -= len_done;
			if ( wait4sendDone(cSoc) == 0 ) {
				EstbPhase[cSoc] = ESTB_TXNRDY;
				break;
			} 
			if ( SndLen[cSoc] == 0 ) {
				// last chunk was sent
				setSn_CR(cSoc, Sn_CR_DISCON);     // Disconnect
				EstbPhase[cSoc] = ESTB_NONE;
			}
			socket_return();
			break;
			
		case ESTB_TXNRDY :
			// wait for previous SendOK acknowledge (Int)
			if ( wait4sendDone(cSoc) == 1 ) {
				if ( SndLen[cSoc] == 0 ) {
					// last chunk was sent
					setSn_CR(cSoc, Sn_CR_DISCON);     // Disconnect
					EstbPhase[cSoc] = ESTB_NONE;
					socket_return();
					break;
				} else
					EstbPhase[cSoc] = ESTB_TRX;
			}
			break;
			
		default:
			break;
		} // End Switch EstbPhase[cSoc]
		break;
	} // End case Sn_SSR(cSoc) == SOCK_ESTABLISHED
						
	case SOCK_CLOSE_WAIT:
		printf("\n\r*Soc_Close_Wait*");
		disconnect(cSoc);
		close(cSoc);
		break;
		
	} // End Switch v = Sn_SSR(cSoc)
	
	cSoc++;
	if ( cSoc >= MAX_SOCK_NUM )	
		cSoc = 0;
}

int	send1st_DS(SOCKET s, uint8 * buf, int len)
{
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

	wiz_write_buf(s, buf, cnt);    // copy data
	
	setSn_TX_WRSR(s, cnt);   			

	return cnt;
}

//int	wait4sendDone(SOCKET s, int length)	
int	wait4sendDone(SOCKET s)	
{
	uint8 isr;
	
	isr=0;
	// wait previous SEND command completion.
	if ( !((isr = getSn_IR(s)) & Sn_IR_SENDOK) ) {
		return 0;
	}
	
	setSn_IR(s, Sn_IR_SENDOK);             // clear Sn_IR_SENDOK	
   
	setSn_CR(s,Sn_CR_SEND);
	
	return 1;
}

void	PrepDwnldData(void)
{
	int i;
	uint32 * p;
	uint32 v;
	
	p = &tmpBuf[0];
	v = 0x12345678;
	
	for ( i = 0; i < (1480/4); i++ ) {
		*p = v;
		p++;
		v += 3;
	}
}
			
