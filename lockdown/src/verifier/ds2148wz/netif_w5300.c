/***
 * \file    w5300.c
 * Implementation of W5300 I/O fucntions
 *
 * This file implements the basic I/O fucntions that access a register of W5300( IINCHIP_REG).
 * 
 * Revision History :
 * ----------  -------  -----------  ----------------------------
 * Date        Version  Author       Description
 * ----------  -------  -----------  ----------------------------
 * 24/03/2008  1.0.0    MidnigthCow  Release with W5300 launching
 * ----------  -------  -----------  ----------------------------
 */
#include "include_netif/w5300.h"
#include "include_netif/ds5300.h"

#include <string.h>

extern	int 		W53ErFlg, sCRcnt, CRdyMax;
extern	uint8   socState[];
extern	int			ssrErr[];

extern	void		delay(unsigned long d);

int printf(const char *format, ...);

/** 
 * TX memory size variables
 */
uint32 TXMEM_SIZE[MAX_SOCK_NUM];

/** 
 * RX memory size variables
 */
uint32 RXMEM_SIZE[MAX_SOCK_NUM];



/***********************************
 * COMMON Register Access Function *
 ***********************************/

/* Interrupt */ 

uint16   getIR(void)
{
   return IINCHIP_READ(IR);
}
void     setIR(uint16 val)
{
   IINCHIP_WRITE(IR, val);   
}

uint16   getIMR(void)
{
   return IINCHIP_READ(IMR);
}
void     setIMR(uint16 mask)
{
   IINCHIP_WRITE(IMR, mask);
}


/* Network Information */

void     getSHAR(uint8 * addr)
{
   addr[0] = (uint8)(IINCHIP_READ(SHAR)>>8);
   addr[1] = (uint8)IINCHIP_READ(SHAR);
   addr[2] = (uint8)(IINCHIP_READ(SHAR2)>>8);
   addr[3] = (uint8)IINCHIP_READ(SHAR2);
   addr[4] = (uint8)(IINCHIP_READ(SHAR4)>>8);
   addr[5] = (uint8)IINCHIP_READ(SHAR4);
}
void     setSHAR(uint8 * addr)
{
   IINCHIP_WRITE(SHAR,(((uint16)addr[0])<<8)+addr[1]);
   IINCHIP_WRITE(SHAR2,((uint16)addr[2]<<8)+addr[3]);
   IINCHIP_WRITE(SHAR4,((uint16)addr[4]<<8)+addr[5]);
}

void     getGAR(uint8 * addr)
{
	addr[0] = (uint8)(IINCHIP_READ(GAR)>>8);
	addr[1] = (uint8)IINCHIP_READ(GAR);
	addr[2] = (uint8)(IINCHIP_READ(GAR2)>>8);
	addr[3] = (uint8)IINCHIP_READ(GAR2);   
}
void     setGAR(uint8 * addr)
{
	IINCHIP_WRITE(GAR, ((uint16)addr[0]<<8)+(uint16)addr[1]);
	IINCHIP_WRITE(GAR2,((uint16)addr[2]<<8)+(uint16)addr[3]);   
}

void     getSUBR(uint8 * addr)
{
	addr[0] = (uint8)(IINCHIP_READ(SUBR)>>8);
	addr[1] = (uint8)IINCHIP_READ(SUBR);
	addr[2] = (uint8)(IINCHIP_READ(SUBR2)>>8);
	addr[3] = (uint8)IINCHIP_READ(SUBR2);   
}
void     setSUBR(uint8 * addr)
{
	IINCHIP_WRITE(SUBR, ((uint16)addr[0]<<8)+(uint16)addr[1]);
	IINCHIP_WRITE(SUBR2,((uint16)addr[2]<<8)+(uint16)addr[3]);   
}

void     getSIPR(uint8 * addr)
{
	addr[0] = (uint8)(IINCHIP_READ(SIPR)>>8);
	addr[1] = (uint8)IINCHIP_READ(SIPR);
	addr[2] = (uint8)(IINCHIP_READ(SIPR2)>>8);
	addr[3] = (uint8)IINCHIP_READ(SIPR2);	
}
void     setSIPR(uint8 * addr)
{
	IINCHIP_WRITE(SIPR,((uint16)addr[0]<<8)+(uint16)addr[1]);
	IINCHIP_WRITE(SIPR2,((uint16)addr[2]<<8)+(uint16)addr[3]);   
}


/* Retransmittion */

uint16   getRTR(void)
{
   return IINCHIP_READ(RTR);
}
void     setRTR(uint16 timeout)
{
	IINCHIP_WRITE(RTR,timeout);   
}

uint8    getRCR(void)
{
   return (uint8)IINCHIP_READ(RCR);
}
void     setRCR(uint8 retry)
{
   IINCHIP_WRITE(RCR,retry);
}

/* PPPoE */
uint16   getPATR(void)
{
   return IINCHIP_READ(PATR);
}

uint8    getPTIMER(void)
{
   return (uint8)IINCHIP_READ(PTIMER);
}
void     setPTIMER(uint8 time)
{
   IINCHIP_WRITE(PTIMER,time);
}

uint8    getPMAGICR(void)
{
   return (uint8)IINCHIP_READ(PMAGICR);
}
void     setPMAGICR(uint8 magic)
{
   IINCHIP_WRITE(PMAGICR,magic);
}

uint16   getPSIDR(void)
{
   return IINCHIP_READ(PSIDR);
}

void     getPDHAR(uint8* addr)
{
   addr[0] = (uint8)(IINCHIP_READ(PDHAR) >> 8);
   addr[1] = (uint8)IINCHIP_READ(PDHAR);
   addr[2] = (uint8)(IINCHIP_READ(PDHAR2) >> 8);
   addr[3] = (uint8)IINCHIP_READ(PDHAR2);
   addr[4] = (uint8)(IINCHIP_READ(PDHAR4) >> 8);
   addr[5] = (uint8)IINCHIP_READ(PDHAR4);
}


/* ICMP packets */

void     getUIPR(uint8* addr)
{
   addr[0] = (uint8)(IINCHIP_READ(UIPR) >> 8);
   addr[1] = (uint8)IINCHIP_READ(UIPR);
   addr[2] = (uint8)(IINCHIP_READ(UIPR2) >> 8);
   addr[3] = (uint8)IINCHIP_READ(UIPR2);   
}

uint16   getUPORTR(void)
{
   return IINCHIP_READ(UPORTR);
}

uint16   getFMTUR(void)
{
   return IINCHIP_READ(FMTUR);
}


/* PIN "BRYDn" */

uint8    getPn_BRDYR(uint8 p)
{
   return (uint8)IINCHIP_READ(Pn_BRDYR(p));
}
void     setPn_BRDYR(uint8 p, uint8 cfg)
{
   IINCHIP_WRITE(Pn_BRDYR(p),cfg);   
}


uint16   getPn_BDPTHR(uint8 p)
{
   return IINCHIP_READ(Pn_BDPTHR(p));   
}
void     setPn_BDPTHR(uint8 p, uint16 depth)
{
   IINCHIP_WRITE(Pn_BDPTHR(p),depth);
}


/* IINCHIP ID */
uint16   getIDR(void)
{
   return IINCHIP_READ(IDR);
}


/***********************************
 * SOCKET Register Access Function *
 ***********************************/

/* SOCKET control */

uint16   getSn_MR(SOCKET s)
{
   return IINCHIP_READ(Sn_MR(s));
}
void     setSn_MR(SOCKET s, uint16 mode)
{
   IINCHIP_WRITE(Sn_MR(s),mode);
}

uint8    getSn_CR(SOCKET s)
{
   return IINCHIP_READ(Sn_CR(s));
}

void     setSn_CR(SOCKET s, uint16 com)
{
	int cnt=0;
	uint16 v1, v2, v3;
	
	sCRcnt++;
	
	
  IINCHIP_WRITE(Sn_CR(s),com);
  while(IINCHIP_READ(Sn_CR(s))) { // wait until Sn_CR is cleared.
  	cnt++;
  	if ( cnt>CRdyMax ) CRdyMax = cnt;
  	if ( cnt>20000 ) {
	  	v1 = IINCHIP_READ(Sn_CR(s));
	  	v2 = getSn_IR(s);
	  	v3 = getSn_SSR(s);
	  	printf("\n\r##CmdRdy Timeout CRcnt=%d cmd=%04x  S(%d)_CR=%04x  ", 
	  					 sCRcnt, com, s, v1 );
	  	printf("Sn_IR=%02x  ", v2);
	  	printf("Sn_SSR=%02x  ", v3);
	  	
	  	
	  	W53ErFlg = 1;
	  	break;
  	}
	}
}

uint8    getSn_IMR(SOCKET s)
{
   return (uint8)IINCHIP_READ(Sn_IMR(s));
}

void     setSn_IMR(SOCKET s, uint8 mask)
{
   IINCHIP_WRITE(Sn_IMR(s),mask);
}

uint8    getSn_IR(SOCKET s)
{
	uint8 v1;

	v1 = (uint8)IINCHIP_READ(Sn_IR(s)); 
	return v1;
}

void     setSn_IR(SOCKET s, uint8 ir)
{
	IINCHIP_WRITE(Sn_IR(s),ir);   
}


/* SOCKET information */

uint8    getSn_SSR(SOCKET s)
{
  uint8 ssr, ssr1, ssr2;
  ssr = (uint8)IINCHIP_READ(Sn_SSR(s));     // first read
  
  while(1) {
		//delay(5);
		ssr1 = (uint8)IINCHIP_READ(Sn_SSR(s)); // second read
		if(ssr == ssr1) break;                 // if first == sencond, Sn_SSR value is valid.
		ssr2 = (uint8)IINCHIP_READ(Sn_SSR(s));
		
		ssr2 = (uint8)IINCHIP_READ(Sn_SSR(s));
      
		ssr = ssr1;                            // if first <> second, save second value into first.
	}
	if ( (ssr==SOCK_CLOSED) && (ssr != socState[s]) ) {
		ssrErr[s]++;
		if ( ssrErr[s] < 3 ) {
			ssr2 = (uint8)IINCHIP_READ(Sn_SSR(s));
		}
	} 
	return ssr;
}

void     getSn_DHAR(SOCKET s, uint8* addr)
{
   addr[0] = (uint8)(IINCHIP_READ(Sn_DHAR(s))>>8);
   addr[1] = (uint8)IINCHIP_READ(Sn_DHAR(s));
   addr[2] = (uint8)(IINCHIP_READ(Sn_DHAR2(s))>>8);
   addr[3] = (uint8)IINCHIP_READ(Sn_DHAR2(s));
   addr[4] = (uint8)(IINCHIP_READ(Sn_DHAR4(s))>>8);
   addr[5] = (uint8)IINCHIP_READ(Sn_DHAR4(s));
}

void     setSn_DHAR(SOCKET s, uint8* addr)
{
   IINCHIP_WRITE(Sn_DHAR(s),  ((uint16)(addr[0]<<8)) + addr[1]);
   IINCHIP_WRITE(Sn_DHAR2(s), ((uint16)(addr[2]<<8)) + addr[3]);
   IINCHIP_WRITE(Sn_DHAR4(s), ((uint16)(addr[4]<<8)) + addr[5]);
}

uint16   getSn_DPORTR(SOCKET s)
{
   return IINCHIP_READ(Sn_DPORTR(s));
}

void     setSn_DPORTR(SOCKET s, uint16 port)
{
   IINCHIP_WRITE(Sn_DPORTR(s),port);
}

void     getSn_DIPR(SOCKET s, uint8* addr)
{
   addr[0] = (uint8)(IINCHIP_READ(Sn_DIPR(s))>>8);
   addr[1] = (uint8)IINCHIP_READ(Sn_DIPR(s));
   addr[2] = (uint8)(IINCHIP_READ(Sn_DIPR2(s))>>8);
   addr[3] = (uint8)IINCHIP_READ(Sn_DHAR2(s));   
}
void     setSn_DIPR(SOCKET s, uint8* addr)
{
   IINCHIP_WRITE(Sn_DIPR(s),  ((uint16)(addr[0]<<8)) + addr[1]);
   IINCHIP_WRITE(Sn_DIPR2(s), ((uint16)(addr[2]<<8)) + addr[3]);  
}

uint16   getSn_MSSR(SOCKET s)
{
   return IINCHIP_READ(Sn_MSSR(s));
}

void     setSn_MSSR(SOCKET s, uint16 mss)
{
   IINCHIP_WRITE(Sn_MSSR(s),mss);
}


/* SOCKET communication */

uint8    getSn_KPALVTR(SOCKET s)
{
   return (uint8)(IINCHIP_READ(Sn_KPALVTR(s)) >> 8);
}

void     setSn_KPALVTR(SOCKET s, uint8 time)
{
   uint16 keepalive=0;
   keepalive = (IINCHIP_READ(Sn_KPALVTR(s)) & 0x00FF) + ((uint16)time<<8);
   IINCHIP_WRITE(Sn_KPALVTR(s),keepalive);
}

uint32   getSn_TX_WRSR(SOCKET s)
{
   uint32 tx_write_size=0;
   tx_write_size = IINCHIP_READ(Sn_TX_WRSR(s));
   tx_write_size = (tx_write_size << 16) + IINCHIP_READ(Sn_TX_WRSR2(s));
   return tx_write_size;
}

void     setSn_TX_WRSR(SOCKET s, uint32 size)
{
   IINCHIP_WRITE(Sn_TX_WRSR(s), (uint16)(size >> 16));
   IINCHIP_WRITE(Sn_TX_WRSR2(s), (uint16)size);
}

uint32   getSn_TX_FSR(SOCKET s)
{
   uint32 free_tx_size=0;
   uint32 free_tx_size1=0;
   while(1)
   {
      free_tx_size = IINCHIP_READ(Sn_TX_FSR(s));                           // read                                       
      free_tx_size = (free_tx_size << 16) + IINCHIP_READ(Sn_TX_FSR2(s));                                                       
      if(free_tx_size == free_tx_size1) break;                             // if first == sencond, Sn_TX_FSR value is valid.                                                          
      free_tx_size1 = free_tx_size;                                        // save second value into firs                                                    
   }                                                                       
   return free_tx_size;                                                    
}                                                                          

uint32   getSn_RX_RSR(SOCKET s)
{
   uint32 received_rx_size=0;
   uint32 received_rx_size1=1;
   while(1)
   {
      received_rx_size = IINCHIP_READ(Sn_RX_RSR(s));
      received_rx_size = (received_rx_size << 16) + IINCHIP_READ(Sn_RX_RSR2(s)); // read                                       
      if(received_rx_size == received_rx_size1) break;                                                                         
      received_rx_size1 = received_rx_size;                                      // if first == sencond, Sn_RX_RSR value is valid.
   }                                                                             // save second value into firs                
   return received_rx_size;   
}


void     setSn_TX_FIFOR(SOCKET s, uint16 data)
{
   IINCHIP_WRITE(Sn_TX_FIFOR(s),data);
}

uint16   getSn_RX_FIFOR(SOCKET s)
{
   return IINCHIP_READ(Sn_RX_FIFOR(s));
}

uint16   getSn_TX_FIFOR(SOCKET s)
{
   return IINCHIP_READ(Sn_TX_FIFOR(s));
}


/* IP header field */

uint8    getSn_PROTOR(SOCKET s)
{
   return (uint8)IINCHIP_READ(Sn_PROTOR(s));
}
void     setSn_PROTOR(SOCKET s, uint8 pronum)
{
   uint16 protocolnum;
   protocolnum = (IINCHIP_READ(Sn_PROTOR(s)) & 0xFF00) + pronum;
   IINCHIP_WRITE(Sn_PROTOR(s),protocolnum);
}

uint8    getSn_TOSR(SOCKET s)
{
   return (uint8)IINCHIP_READ(Sn_TOSR(s));
}
void     setSn_TOSR(SOCKET s, uint8 tos)
{
   IINCHIP_WRITE(Sn_TOSR(s),tos);
}

uint8    getSn_TTLR(SOCKET s)
{
   return (uint8)IINCHIP_READ(Sn_TTLR(s));
}
void     setSn_TTLR(SOCKET s, uint8 ttl)
{
   IINCHIP_WRITE(Sn_TTLR(s),ttl);
}

uint8    getSn_FRAGR(SOCKET s)
{
   return (uint8)IINCHIP_READ(Sn_FRAGR(s));
}

void     setSn_FRAGR(SOCKET s, uint8 frag)
{
   IINCHIP_WRITE(Sn_FRAGR(s),frag);
}


/*******
 * ETC *
 *******/


/* Internal memory operation */
 
uint8    sysinit(uint8* tx_size, uint8* rx_size)
{
   uint16 i;
   uint16 ssum=0,rsum=0;
   uint mem_cfg = 0;
   
   for(i=0; i < MAX_SOCK_NUM; i++)
   {
      if(tx_size[i] > 64)
      {
      #ifdef __DEF_IINCHIP_DBG__
         printf("Illegal Channel(%d) TX Memory Size.\n\r",i);
      #endif
         return 0;
      }
      if(rx_size[i] > 64)
      {
      #ifdef __DEF_IINCHIP_DBG__         
         printf("Illegal Channel(%d) RX Memory Size.\n\r",i);
      #endif
         return 0;
      }
      ssum += (uint16)tx_size[i];
      rsum += (uint16)rx_size[i];
      TXMEM_SIZE[i] = ((uint32)tx_size[i]) << 10;
      RXMEM_SIZE[i] = ((uint32)rx_size[i]) << 10;
   }
   if( (ssum % 8) || ((ssum + rsum) != 128) )
   {
   #ifdef __DEF_IINCHIP_DBG__
      printf("Illegal Memory Allocation\n\r");
   #endif
      return 0;
      //return 1;
   }
   
   IINCHIP_WRITE(TMS01R,((uint16)tx_size[0] << 8) + (uint16)tx_size[1]);
   IINCHIP_WRITE(TMS23R,((uint16)tx_size[2] << 8) + (uint16)tx_size[3]);
   IINCHIP_WRITE(TMS45R,((uint16)tx_size[4] << 8) + (uint16)tx_size[5]);
   IINCHIP_WRITE(TMS67R,((uint16)tx_size[6] << 8) + (uint16)tx_size[7]);
   
   IINCHIP_WRITE(RMS01R,((uint16)rx_size[0] << 8) + (uint16)rx_size[1]);
   IINCHIP_WRITE(RMS23R,((uint16)rx_size[2] << 8) + (uint16)rx_size[3]);
   IINCHIP_WRITE(RMS45R,((uint16)rx_size[4] << 8) + (uint16)rx_size[5]);
   IINCHIP_WRITE(RMS67R,((uint16)rx_size[6] << 8) + (uint16)rx_size[7]);
   
   for(i=0; i <ssum/8 ; i++)
   {
      mem_cfg <<= 1;
      mem_cfg |= 1;
   }
   
   IINCHIP_WRITE(MTYPER,mem_cfg);
   
   #ifdef __DEF_IINCHIP_DBG_
   	/***
			printf("Total TX Memory Size = %dKB\n\r",ssum);
      printf("Total RX Memory Size = %dKB\n\r",rsum);
      printf("Ch : TX SIZE : RECV SIZE\n\r");
      printf("%02d : %07dKB : %07dKB \n\r", 0, (uint8)(IINCHIP_READ(TMS01R)>>8),(uint8)(IINCHIP_READ(RMS01R)>>8));
      printf("%02d : %07dKB : %07dKB \n\r", 1, (uint8)IINCHIP_READ(TMS01R),(uint8)IINCHIP_READ(RMS01R));
      printf("%02d : %07dKB : %07dKB \n\r", 2, (uint8)(IINCHIP_READ(TMS23R)>>8),(uint8)(IINCHIP_READ(RMS23R)>>8));
      printf("%02d : %07dKB : %07dKB \n\r", 3, (uint8)IINCHIP_READ(TMS23R),(uint8)IINCHIP_READ(RMS23R));
      printf("%02d : %07dKB : %07dKB \n\r", 4, (uint8)(IINCHIP_READ(TMS45R)>>8),(uint8)(IINCHIP_READ(RMS45R)>>8));
      printf("%02d : %07dKB : %07dKB \n\r", 5, (uint8)IINCHIP_READ(TMS45R),(uint8)IINCHIP_READ(RMS45R));
      printf("%02d : %07dKB : %07dKB \n\r", 6, (uint8)(IINCHIP_READ(TMS67R)>>8),(uint8)(IINCHIP_READ(RMS67R)>>8));
      printf("%02d : %07dKB : %07dKB \n\r", 7, (uint8)IINCHIP_READ(TMS67R),(uint8)IINCHIP_READ(RMS67R));
      printf("\n\rMTYPER=%04x\n\r",IINCHIP_READ(MTYPER));
    ****/
   #endif
   
   return 1;
}

uint32   getIINCHIP_TxMAX(SOCKET s)
{
   return TXMEM_SIZE[s];
}

uint32   getIINCHIP_RxMAX(SOCKET s)
{
   return RXMEM_SIZE[s];
}


void  wait_1us(uint32 us)
{
   uint32 i,j;
   for(i = 0; i < us ; i++)
   {
      for(j = 0; j < 100; j++);
   }
}

void  wait_1ms(uint32 ms)
{
   uint32 i;
   for(i = 0; i < ms ; i++)
   {
     wait_1us(1000);
   }
   
}

void  wait_10ms(uint32 ms)
{
   uint32 i;
   for(i = 0; i < ms ; i++)
   {
     wait_1ms(10);
   }
}
