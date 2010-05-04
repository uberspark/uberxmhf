/**
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
 
 
#include "socket.h"
#include "string.h"
#include "ds5300.h"

int printf(const char *format, ...);

extern	void		LogWr( uint16 data );
extern	void		LogWrTim( void );
extern	void		WrDBMarker (uint16 val);

extern	int W53ErFlg;
extern	uint32 miliSec, msecEstb;
extern	uint16	DB_MarkerU;


/** 
 * Variable for temporary source port number 
 */
uint16   iinchip_source_port;

uint8   check_sendok_flag[MAX_SOCK_NUM];		//The flag to check if first send.
uint8   socState[MAX_SOCK_NUM];
int			ssrErr[MAX_SOCK_NUM];

uint8    socket(SOCKET s, uint8 protocol, uint16 port, uint16 flag)
{
	//DB_MarkerU = 0x11;
	//WrDBMarker(0x11);
	
  IINCHIP_WRITE(Sn_MR(s),(uint16)(protocol | flag)); // set Sn_MR with protocol & flag
  
	LogWr(0x11); LogWr(s); LogWrTim();
	
  if (port != 0) IINCHIP_WRITE(Sn_PORTR(s),port);
  else  {
    iinchip_source_port++;     // if don't set the source port, set local_port number.
    IINCHIP_WRITE(Sn_PORTR(s),iinchip_source_port);
  }
	setSn_CR(s, Sn_CR_OPEN);      // open s-th SOCKET 
   
	check_sendok_flag[s] = 1;     // initialize the sendok flag.
   
	#ifdef __DEF_IINCHIP_DBG__
		//printf("\n\r%d : Sn_MR=0x%04x,Sn_PORTR=0x%04x(%d),Sn_SSR=%04x",s,IINCHIP_READ(Sn_MR(s)),IINCHIP_READ(Sn_PORTR(s)),IINCHIP_READ(Sn_PORTR(s)),getSn_SSR(s));
	#endif
	
	return 1;   
}

void     close(SOCKET s)
{
	//DB_MarkerU = 0x26;
	//WrDBMarker(0x26);
	
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
				sendto(s,(uint8*)"x",1,destip,0x3000); // send the dummy data to an unknown destination(0.0.0.1).
			}
			//delay(1000000);				// wait 100msec
			wait_10ms(10);
		}
	}
	
	setSn_IR(s ,0x00FF);          // Clear the remained interrupt bits.
	setSn_CR(s ,Sn_CR_CLOSE);     // Close s-th SOCKET 
 
}

uint8    connect(SOCKET s, uint8 * addr, uint16 port)
{
	//DB_MarkerU = 0x21;
	//WrDBMarker(0x21);
	
	LogWr(0x21); LogWr(s); LogWrTim();
	
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
	LogWr(0x25); LogWr(s); LogWrTim();
	
	#ifdef __DEF_IINCHIP_DBG__
		//printf( "\n\rdisc_%d t=%d ", s, (int)(miliSec-msecEstb) );
	#endif
  
	//DB_MarkerU = 0x25;
	//WrDBMarker(0x25);
	
	setSn_CR(s,Sn_CR_DISCON);     // Disconnect
}

uint8    listen(SOCKET s)
{
	//DB_MarkerU = 0x22;
	//WrDBMarker(0x22);
	
	LogWr(0x22); LogWr(s); LogWrTim();
	
  if (getSn_SSR(s) != SOCK_INIT)    {
      #ifdef __DEF_IINCHIP_DBG__
         printf("\n\r%d : SOCKET is not created!",s);
      #endif
      return 0;
  }
  
	setSn_CR(s,Sn_CR_LISTEN);     // listen
   
  return 1;
}  
 
uint32   send(SOCKET s, uint8 * buf, uint32 len)
{
  uint8 status=0;
  uint32 ret=0;
  uint32 freesize=0;
  
	//DB_MarkerU = 0x23;
	//WrDBMarker(0x23);
  
	//LogWr(0x23); LogWr(s); LogWrTim();
   
  #ifdef __DEF_IINCHIP_DBG__
      uint32 loopcnt = 0;
      //printf("\n\rsend(%d) len=%d Tim=%04x ", s, (int)len, (uint16)(miliSec-msecEstb) );
  #endif

	ret = len;
	if (len > getIINCHIP_TxMAX(s)) ret = getIINCHIP_TxMAX(s); // check size not to exceed MAX size.

	/*
  * \n\rote if you want to use non blocking function, <b>"do{}while(freesize < ret)"</b> code block 
  * can be replaced with the below code. \n\r
  * \code 
  *       while((freesize = getSn_TX_FSR(s))==0); 
  *       ret = freesize;
  * \endcode
  */
  // -----------------------
  // NOTE : CODE BLOCK START
	do  {
    freesize = getSn_TX_FSR(s);
    status = getSn_SSR(s);
    #ifdef __DEF_IINCHIP_DBG__
			//printf("\n\r%d : freesize=%x", s, (unsigned int)freesize);
			if(loopcnt++ > 0x0010000) { 
				printf("\n\r%d : freesize=%x,status=%04x", s, (unsigned int)freesize,status);
				printf("\n\r%d:Send Size=%08lx(%d)  ", s, ret,( int)ret);
				printf("MR=%04x", getMR());
				loopcnt = 0;
			}
		#endif
    if ((status != SOCK_ESTABLISHED) && (status != SOCK_CLOSE_WAIT)) return 0;
	} while (freesize < ret);
	// NOTE : CODE BLOCK END
   
	wiz_write_buf(s, buf, ret);                 // copy data

	#ifdef __DEF_IINCHIP_DBG__
		loopcnt=0;
	#endif   
   
	if(!check_sendok_flag[s])  {              // if first send, skip.
		uint8 isr=0;
		while ( !((isr = getSn_IR(s)) & Sn_IR_SENDOK) ) {	// wait previous SEND command completion.
			#ifdef __DEF_IINCHIP_DBG__
			if(loopcnt++ > 0x010000) {
				//LogWr(0x555); LogWr(isr); LogWrTim();
				
				printf("\n\rWait4SendOK %d: Sn_SSR=%04x) ", s, status);
				printf("SnIR=%02x Size=%08lx(%d)  ", isr, ret, (int)ret);
				loopcnt = 0;
				W53ErFlg = 1;
				return 0;
			}
			#endif
		
    	if (getSn_SSR(s) == SOCK_CLOSED)  {  // check timeout or abnormal closed.
				#ifdef __DEF_IINCHIP_DBG__
					printf("\n\r%d : Send Fail. SOCK_CLOSED",s);
				#endif
				return 0;
			}
		}
		//printf("\n\r++SndRdy %d: loopcnt=%d ", s, (int)loopcnt);
		setSn_IR(s, Sn_IR_SENDOK);             // clear Sn_IR_SENDOK	
	}
	else check_sendok_flag[s] = 0;
   
  // send
	setSn_TX_WRSR(s,ret);   
	setSn_CR(s,Sn_CR_SEND);
   
	return ret;
}

uint32   recv(SOCKET s, uint8 * buf, uint32 len)
{
  uint16 pack_size=0;
  uint16 v1, tps;

	//WrDBMarker(0x24);
	//DB_MarkerU = 0x24;
	
  //LogWr(0x24); LogWr(s); LogWrTim();
	
  #ifdef __DEF_IINCHIP_DBG__
		//printf("\n\r%d : recv() len=%d Tim=%04x ", s, (int)len, (uint16)(miliSec-msecEstb) );
	#endif
	
  v1 = IINCHIP_READ(Sn_MR(s)); 
	if( v1 & Sn_MR_ALIGN ) {
		wiz_read_buf(s, buf, (uint32)len);
		//printf("\n\rAlign len=%d", (int)len);
		setSn_CR(s,Sn_CR_RECV);
		return len;
	}
   
	wiz_read_buf(s, (uint8*)&pack_size, 2);        // extract the PACKET-INFO(DATA packet length)
	pack_size = ((((pack_size << 8 ) & 0xFF00)) | ((pack_size >> 8)& 0x00FF));
	if ( pack_size>1024 ) {
		printf("\n\rPack_size too big %d", pack_size);
		pack_size = 1024;
	}
	tps = pack_size; 											// ***JD tps keeps original packet size without adjustment to even		 
	if ( pack_size&0x01 ) pack_size++;
	
	wiz_read_buf(s, buf, (uint32)pack_size);     // copy data 
   
  setSn_IR(s, Sn_IR_RECV);             // clear Sn_IR_RECV	***JD
   
	setSn_CR(s,Sn_CR_RECV);                      // recv
	
  #ifdef __DEF_IINCHIP_DBG__
		//printf("  recv_end Tim=%04x ", (uint16)(miliSec-msecEstb) );
	#endif
	
   
   /*
   * \warning  send a packet for updating window size.
   */
   // ------------------------
   // WARNING CODE BLOCK START 
   //if(getSn_RX_RSR(s) == 0)                     // check if the window size is full or not
   //{ /* Sn_RX_RSR can be compared with another value instead of ¡®0¡¯,
   //   according to the host performance of receiving data */
   //   printf("  warning  ");
   //   setSn_TX_WRSR(s,1);                       // size : 1 byte dummy size
   //   IINCHIP_WRITE(Sn_TX_FIFOR(s),0x0000);     // write dummy data into tx memory
   //   setSn_CR(s,Sn_CR_SEND);                   // send                         
   //   while(!(getSn_IR(s) & Sn_IR_SENDOK));     // wait SEND command completion 
   //   setSn_IR(s,Sn_IR_SENDOK);                 // clear Sn_IR_SENDOK bit       
   //}                                                                            
   // WARNING CODE BLOCK END
   
   return (uint32)tps;
}

uint32   sendto(SOCKET s, uint8 * buf, uint32 len, uint8 * addr, uint16 port)
{
	uint8 status=0;
	uint8 isr=0;
	uint32 ret=0;
   
	#ifdef __DEF_IINCHIP_DBG__
		printf("\n\r%d : sendto():%d.%d.%d.%d(%d), len=%d",s, addr[0], addr[1], addr[2], addr[3] , port, (int)len);
	#endif
  
   if
   (
      ((addr[0] == 0x00) && (addr[1] == 0x00) && (addr[2] == 0x00) && (addr[3] == 0x00)) ||
      ((port == 0x00)) ||(len == 0)
   ) 
   {
      #ifdef __DEF_IINCHIP_DBG__
         printf("\n\r%d : Fail[%d.%d.%d.%d, %.d, %d]",s, addr[0], addr[1], addr[2], addr[3] , port, (int)len);
      #endif
      return 0;
   }
   
   
   if (len > getIINCHIP_TxMAX(s)) ret = getIINCHIP_TxMAX(s); // check size not to exceed MAX size.
   else ret = len;
   
   // set destination IP address
   IINCHIP_WRITE(Sn_DIPR(s),(((uint16)addr[0])<<8) + (uint16) addr[1]);
   IINCHIP_WRITE(Sn_DIPR2(s),(((uint16)addr[2])<<8) + (uint16) addr[3]);
   // set destination port number
   IINCHIP_WRITE(Sn_DPORTR(s),port);
   
   wiz_write_buf(s, buf, ret);                              // copy data
   // send
   setSn_TX_WRSR(s,ret);
   setSn_CR(s, Sn_CR_SEND);
   
   while (!((isr = getSn_IR(s)) & Sn_IR_SENDOK))            // wait SEND command completion
   {
      status = getSn_SSR(s);                                // warning ---------------------------------------
      if ((status == SOCK_CLOSED) || (isr & Sn_IR_TIMEOUT)) // Sn_IR_TIMEOUT causes the decrement of Sn_TX_FSR
      {                                                     // -----------------------------------------------
         #ifdef __DEF_IINCHIP_DBG__
            printf("\n\r%d: send fail.status=0x%02x,isr=%02x", s, status, isr);
         #endif
         setSn_IR(s,Sn_IR_TIMEOUT);
         return 0;
      }
   }
   setSn_IR(s, Sn_IR_SENDOK); // Clear Sn_IR_SENDOK
   
   #ifdef __DEF_IINCHIP_DBG__		
      printf("\n\r%d : send()end", s);
   #endif       
   
   return ret;   
}

uint32   recvfrom(SOCKET s, uint8 * buf, uint32 len, uint8 * addr, uint16  *port)
{
   uint16 head[4];
   uint32 data_len=0;
   uint16 crc[2];
   
   #ifdef __DEF_IINCHIP_DBG__
      printf("\n\rrecvfrom()");
   #endif
   
   if ( len > 0 )
   {
      switch (IINCHIP_READ(Sn_MR(s)) & 0x07)       // check the mode of s-th SOCKET
      {                                            // -----------------------------
         case Sn_MR_UDP :                          // UDP mode 
            wiz_read_buf(s, (uint8*)head, 8);      // extract the PACKET-INFO
            // read peer's IP address, port number.
            //if(*((vuint16*)MR) & MR_FS)            // check FIFO swap bit
            //{
               head[0] = ((((head[0] << 8 ) & 0xFF00)) | ((head[0] >> 8)& 0x00FF));
               head[1] = ((((head[1] << 8 ) & 0xFF00)) | ((head[1] >> 8)& 0x00FF));
               head[2] = ((((head[2] << 8 ) & 0xFF00)) | ((head[2] >> 8)& 0x00FF));
               head[3] = ((((head[3] << 8 ) & 0xFF00)) | ((head[3] >> 8)& 0x00FF));
            //}
            addr[0] = (uint8)(head[0] >> 8);       // destination IP address
            addr[1] = (uint8)head[0];
            addr[2] = (uint8)(head[1]>>8);
            addr[3] = (uint8)head[1];
            *port = head[2];                       // destination port number
            data_len = (uint32)head[3];            // DATA packet length
            
            #ifdef __DEF_IINCHIP_DBG__
               printf("\n\rUDP msg arrived:%d(0x%04x) ", (int)data_len, (uint16)data_len);
               //printf("src Port : %d ", *port);
               //printf("src IP : %d.%d.%d.%d", addr[0], addr[1], addr[2], addr[3]);
            #endif
   
            wiz_read_buf(s, buf, data_len);        // data copy.
            break;
                                                   // -----------------------
         case Sn_MR_IPRAW :                        // IPRAW mode
            wiz_read_buf(s, (uint8*)head, 6);      // extract the PACKET-INFO 
            //if(*((vuint16*)MR) & MR_FS)            // check FIFO swap bit
            //{
               head[0] = ((((head[0] << 8 ) & 0xFF00)) | ((head[0] >> 8)& 0x00FF));
               head[1] = ((((head[1] << 8 ) & 0xFF00)) | ((head[1] >> 8)& 0x00FF));
               head[2] = ((((head[2] << 8 ) & 0xFF00)) | ((head[2] >> 8)& 0x00FF));
            //}   			
            addr[0] = (uint8)(head[0] >> 8);       // destination IP address
            addr[1] = (uint8)head[0];
            addr[2] = (uint8)(head[1]>>8);
            addr[3] = (uint8)head[1];
            data_len = (uint32)head[2];            // DATA packet length
            
            #ifdef __DEF_IINCHIP_DBG__
               printf("\n\rIP RAW msg arrived");
               printf("\n\rsource IP : %d.%d.%d.%d", addr[0], addr[1], addr[2], addr[3]);
            #endif
            
            wiz_read_buf(s, buf, data_len);        // data copy.
            break;                                 
                                                   // -----------------------
         case Sn_MR_MACRAW :                       // MACRAW mode
            wiz_read_buf(s,(uint8*)head,2);        // extract the PACKET-INFO
            //if(*((vuint16*)MR) & MR_FS)            // check FIFO swap bit
               head[0] = ((((head[0] << 8 ) & 0xFF00)) | ((head[0] >> 8)& 0x00FF));
            data_len = (uint32)head[0];            // DATA packet length
            wiz_read_buf(s, buf, data_len);        // data copy.
            wiz_read_buf(s,(uint8*)crc, 4);        // extract CRC data and ignore it.

            break;
         default :
            break;
      }
      setSn_CR(s,Sn_CR_RECV);                      // recv
   }
   #ifdef __DEF_IINCHIP_DBG__
      printf("\n\rrecvfrom() end ..");
   #endif
   
   return data_len;   
}
