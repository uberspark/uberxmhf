/***
 * \file    socket.c
 *   Implemetation of WIZnet SOCKET API fucntions
 *
 * This file implements the WIZnet SOCKET API functions that is used in your internat application program.
 * 
 * Revision History :
 * ----------  -------  -----------  ----------------------------
 * Date        Version  Author       Description
 * ----------  -------  -----------  ----------------------------
 * 24/03/2008  1.0.0    MidnigthCow  Release with W5300 launching
 * ----------  -------  -----------  ----------------------------
 */
 
 
#include "include_netif/socket.h"
#include "string.h"
#include "include_netif/ds5300.h"

#define	IBUF_SIZE		1500

int printf(const char *format, ...);

extern	int W53ErFlg;


/** 
 * Variable for temporary source port number 
 */
uint16   iinchip_source_port;

uint8   socState[MAX_SOCK_NUM];
int			ssrErr[MAX_SOCK_NUM];

uint8    socket(SOCKET s, uint8 protocol, uint16 port, uint16 flag)
{
  IINCHIP_WRITE(Sn_MR(s),(uint16)(protocol | flag)); // set Sn_MR with protocol & flag
  
  if (port != 0) IINCHIP_WRITE(Sn_PORTR(s),port);
  else  {
    iinchip_source_port++;     // if don't set the source port, set local_port number.
    IINCHIP_WRITE(Sn_PORTR(s),iinchip_source_port);
  }
	setSn_CR(s, Sn_CR_OPEN);      // open s-th SOCKET 
   
	return 1;   
}

void     close(SOCKET s)
{
	
	// M_08082008 : It is fixed the problem that Sn_SSR cannot be changed a undefined value to the defined value.
	//              Refer to Errata of W5300
	//Check if the transmit data is remained or not.
	if( ((getSn_MR(s)& 0x0F) == Sn_MR_TCP) && (getSn_TX_FSR(s) != getIINCHIP_TxMAX(s)) ) { 
		uint16 loop_cnt =0;
		#ifdef __DEF_IINCHIP_DBG__
      printf("\n\rClose() Fix");
		#endif
		while(getSn_TX_FSR(s) != getIINCHIP_TxMAX(s)) {
			if(loop_cnt++ > 10) {
				uint8 destip[4];
				getSIPR(destip);
				socket(s,Sn_MR_UDP,0x3000,0);
				//sendto(s,(uint8*)"x",1,destip,0x3000); // send the dummy data to an unknown destination(0.0.0.1).
			}
			wait_10ms(10);
		}
	}
	
	setSn_IR(s ,0x00FF);          // Clear the remained interrupt bits.
	setSn_CR(s ,Sn_CR_CLOSE);     // Close s-th SOCKET 
 
}

uint8    connect(SOCKET s, uint8 * addr, uint16 port)
{
  if  (
      ((addr[0] == 0xFF) && (addr[1] == 0xFF) && (addr[2] == 0xFF) && (addr[3] == 0xFF)) ||
      ((addr[0] == 0x00) && (addr[1] == 0x00) && (addr[2] == 0x00) && (addr[3] == 0x00)) ||
      (port == 0x00) )
  {
      #ifdef __DEF_IINCHIP_DBG__
         printf("\n\r%d : Fail[invalid ip,port]",s);
      #endif
      return 0;
   }
   
   // set destination IP 
   IINCHIP_WRITE(Sn_DIPR(s),((uint16)addr[0]<<8)+(uint16)addr[1]);
   IINCHIP_WRITE(Sn_DIPR2(s),((uint16)addr[2]<<8)+(uint16)addr[3]);
   // set destination port number
   IINCHIP_WRITE(Sn_DPORTR(s),port);
   
   // Connect
   setSn_CR(s,Sn_CR_CONNECT);

   return 1;   
}

void     disconnect(SOCKET s)
{

	setSn_CR(s,Sn_CR_DISCON);     // Disconnect
}

uint8    listen(SOCKET s)
{

  if (getSn_SSR(s) != SOCK_INIT)    {
      #ifdef __DEF_IINCHIP_DBG__
         printf("\n\r%d : SOCKET is not created!",s);
      #endif
      return 0;
  }
  
	setSn_CR(s,Sn_CR_LISTEN);     // listen
   
  return 1;
}  

uint32   recv(SOCKET s, uint8 * buf, uint32 len)
{
  uint16 pack_size=0;
  uint16 v1, tps;

  v1 = IINCHIP_READ(Sn_MR(s)); 
	if( v1 & Sn_MR_ALIGN ) {
		wiz_read_buf(s, buf, (uint32)len);
		setSn_CR(s,Sn_CR_RECV);
		return len;
	}
   
	wiz_read_buf(s, (uint8*)&pack_size, 2);        // extract the PACKET-INFO(DATA packet length)
	
  
  //pack_size = ((((pack_size << 8 ) & 0xFF00)) | ((pack_size >> 8)& 0x00FF));
  
  if( (*(vint16*)MR) & MR_FS )
      pack_size = ((((pack_size << 8 ) & 0xFF00)) | ((pack_size >> 8)& 0x00FF));
   
  printf("recv %d:pack_size=%d\r\n",s,pack_size);

  
	if ( pack_size>IBUF_SIZE ) {
		printf("\n\rPack_size too big %d", pack_size);
		pack_size = IBUF_SIZE;
	}
	tps = pack_size; 											// ***JD tps keeps original packet size without adjustment to even	
		 
	if ( pack_size&0x01 ) pack_size++;
	
	wiz_read_buf(s, buf, pack_size);     // copy data 
	setSn_CR(s,Sn_CR_RECV);                      // recv
	
	return (uint32)tps;
}

int	send(SOCKET s, uint8 * buf, int len)
{
	//int cnt, txfree_size;
		
	//txfree_size = (int)getSn_TX_FSR(s);
	//if ( txfree_size == 0 ) 
	//	return 0;
			
	//cnt = len;
	//if ( cnt > txfree_size )	cnt = txfree_size;
	//if ( cnt > TXWRMAX )	cnt = TXWRMAX;

	return ( wiz_write_buf(s, buf, len) );    // copy data
	
	//setSn_TX_WRSR(s, cnt);   			

	//return cnt;
}
