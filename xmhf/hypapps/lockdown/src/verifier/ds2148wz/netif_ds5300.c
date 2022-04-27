/**
 * \file    ds5300.c
 * Implementation of DS customized W5300 I/O fucntions
 *
 * This file implements the basic I/O fucntions that access a register of W5300( IINCHIP_REG).
 * 
 * Revision History :
 * ----------  -------  --------  --------------------------------------------------
 * Date        Version  Author       Description
 * ----------  -------  --------  --------------------------------------------------
 * 7/05/2008  1.0.0    JD				  Release with W5300 launching
 * 7/28/2009  1.1.0    JD				  Faster wiz_write_buf (linear block of 4 bytes) and
																		wiz_read_buf (linear block of 8 bytes)
 * ----------  -------  --------  --------------------------------------------------
 */
#include	"include_netif/w5300.h"
#include	"arm2148/lpc21xx.h"
#include	"arm2148/processor.h"

#define IINCHIP_ISR_DISABLE()
#define IINCHIP_ISR_ENABLE()	


#define LATCH_STRB	(1 << 24)
#define WIZ_CS			(1 << 25)
#define WIZ_ON			(1 << 23)
#define WIZ_RES			(1 << 21)
#define WIZ_RD			(1 << 20)
#define WIZ_WR			(1 << 19)
#define WIZ_A0			(1 << 16)
#define WIZ_A1			(1 << 17)
#define WIZ_A2			(1 << 18)

#define MR0_REG			00
#define MR1_REG			01

#define IDM_AR0_		02
#define IDM_AR1_		03
#define IDM_DR0_		04
#define IDM_DR1_		05

#define WR5300_MR0	(MR0_REG<<16)|WIZ_RD|WIZ_RES|WIZ_ON
#define W5300_MR0IDLE	(MR0_REG<<16)|WIZ_RD|WIZ_WR|WIZ_RES|WIZ_ON

#define WR5300_MR1	(MR1_REG<<16)|WIZ_RD|WIZ_RES|WIZ_ON
#define W5300_MR1IDLE	(MR1_REG<<16)|WIZ_RD|WIZ_WR|WIZ_RES|WIZ_ON

#define WR5300_AR0	(IDM_AR0_<<16)|WIZ_RD|WIZ_RES|WIZ_ON
#define W5300_AR0IDLE	(IDM_AR0_<<16)|WIZ_RD|WIZ_WR|WIZ_RES|WIZ_ON

#define WR5300_AR1	(IDM_AR1_<<16)|WIZ_RD|WIZ_RES|WIZ_ON
#define W5300_AR1IDLE	(IDM_AR1_<<16)|WIZ_RD|WIZ_WR|WIZ_RES|WIZ_ON

#define WR5300_DR0	(IDM_DR0_<<16)|WIZ_RD|WIZ_RES|WIZ_ON
#define W5300_DR0IDLE	(IDM_DR0_<<16)|WIZ_RD|WIZ_WR|WIZ_RES|WIZ_ON
#define WR5300_DR1	(IDM_DR1_<<16)|WIZ_RD|WIZ_RES|WIZ_ON	
#define W5300_DR1IDLE	(IDM_DR1_<<16)|WIZ_RD|WIZ_WR|WIZ_RES|WIZ_ON	

#define RD5300_DR0	(IDM_DR0_<<16)|WIZ_WR|WIZ_RES|WIZ_ON
#define R5300_DR0IDLE	(IDM_DR0_<<16)|WIZ_RD|WIZ_WR|WIZ_RES|WIZ_ON
#define RD5300_DR1	(IDM_DR1_<<16)|WIZ_WR|WIZ_RES|WIZ_ON	
#define R5300_DR1IDLE	(IDM_DR1_<<16)|WIZ_RD|WIZ_WR|WIZ_RES|WIZ_ON	

#define RD5300_AR0	(IDM_AR0_<<16)|WIZ_WR|WIZ_RES|WIZ_ON
#define RD5300_AR1	(IDM_AR1_<<16)|WIZ_WR|WIZ_RES|WIZ_ON	

#define LATCH_STRBa	(1 << 8)
#define WIZ_CSa			(1 << 9)
#define WIZ_ONa			(1 << 7)
#define WIZ_RESa		(1 << 5)
#define WIZ_RDa			(1 << 4)
#define WIZ_WRa			(1 << 3)

#define LATCH_STRBb	(1 << 0)
#define WIZ_CSb			(1 << 1)

#define W530_MR0a			MR0_REG|WIZ_RDa|WIZ_RESa|WIZ_ONa
#define W530_MR0IDLEa	MR0_REG|WIZ_RDa|WIZ_WRa|WIZ_RESa|WIZ_ONa
#define W530_MR1a			MR1_REG|WIZ_RDa|WIZ_RESa|WIZ_ONa
#define W530_MR1IDLEa	MR1_REG|WIZ_RDa|WIZ_WRa|WIZ_RESa|WIZ_ONa

#define R530_MR0a			MR0_REG|WIZ_WRa|WIZ_RESa|WIZ_ONa
#define R530_MR0IDLEa	MR0_REG|WIZ_RDa|WIZ_WRa|WIZ_RESa|WIZ_ONa
#define R530_MR1a			MR1_REG|WIZ_WRa|WIZ_RESa|WIZ_ONa	
#define R530_MR1IDLEa	MR1_REG|WIZ_RDa|WIZ_WRa|WIZ_RESa|WIZ_ONa	

#define W530_AR0a			IDM_AR0_|WIZ_RDa|WIZ_RESa|WIZ_ONa
#define W530_AR0IDLEa	IDM_AR0_|WIZ_RDa|WIZ_WRa|WIZ_RESa|WIZ_ONa
#define W530_AR1a			IDM_AR1_|WIZ_RDa|WIZ_RESa|WIZ_ONa
#define W530_AR1IDLEa	IDM_AR1_|WIZ_RDa|WIZ_WRa|WIZ_RESa|WIZ_ONa

#define W530_DR0a			IDM_DR0_|WIZ_RDa|WIZ_RESa|WIZ_ONa
#define W530_DR0IDLEa	IDM_DR0_|WIZ_RDa|WIZ_WRa|WIZ_RESa|WIZ_ONa
#define W530_DR1a			IDM_DR1_|WIZ_RDa|WIZ_RESa|WIZ_ONa	
#define W530_DR1IDLEa	IDM_DR1_|WIZ_RDa|WIZ_WRa|WIZ_RESa|WIZ_ONa	

#define R530_DR0a			IDM_DR0_|WIZ_WRa|WIZ_RESa|WIZ_ONa
#define R530_DR0IDLEa	IDM_DR0_|WIZ_RDa|WIZ_WRa|WIZ_RESa|WIZ_ONa
#define R530_DR1a			IDM_DR1_|WIZ_WRa|WIZ_RESa|WIZ_ONa	
#define R530_DR1IDLEa	IDM_DR1_|WIZ_RDa|WIZ_WRa|WIZ_RESa|WIZ_ONa	

#define R530_AR0a			IDM_AR0_|WIZ_WRa|WIZ_RESa|WIZ_ONa
#define R530_AR1a			IDM_AR1_|WIZ_WRa|WIZ_RESa|WIZ_ONa	
#define R530_AR0IDLEa	IDM_AR0_|WIZ_RDa|WIZ_WRa|WIZ_RESa|WIZ_ONa
#define R530_AR1IDLEa	IDM_AR1_|WIZ_RDa|WIZ_WRa|WIZ_RESa|WIZ_ONa

#define NOP_3	\
	asm volatile ("nop");\
	asm volatile ("nop");\
	asm volatile ("nop");

#define NOP_2	\
	asm volatile ("nop");\
	asm volatile ("nop");



extern 	int 		SpurIntCnt, CRdyMax;
extern	int			W53ErFlg, Tst1Flag;

extern	uint8		EstbPhase[];
extern 	int			ssrErr[];

extern	void	delay(unsigned long d);

extern	int printf(const char *format, ...);

//  Forward prototypes
void 		P1Init(void);
void    setMR(uint16 val);
uint16  getMR(void);
void  	iinchip_init(void);
uint16  IINCHIP_READ(uint32 addr);
void    IINCHIP_WRITE(uint32 addr,uint16 data);
uint32  wiz_write_buf(SOCKET s, uint8* buf,uint32 len);
uint32  wiz_read_buf(SOCKET s, uint8* buf,uint32 len);
int 		Rd5300_bl(uint16 addr, uint8* buf, int len);
void 		W5300PwrOn(void);
void 		W5300PwrOff(void);
void 		W5300Init2(void);



/***
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

***/    

void P1Init(void)
{
  // Initialize P1.16 .. P1.32
  // P1.16-P1.24:GPIO or ETM Port, P1.24:GPIO, P1.26-P1.31: GPIO or JTAG Port
  
  PINSEL2    = 0x4;						// P1.16 .. P1.25 GPIOs, P1.26..P1.31 Jtag port
  FIO1DIR    = 0x03FF0000;				// P1.16 .. P1.25 Output
  FIO1PIN    = WIZ_ON|WIZ_RD|WIZ_WR|WIZ_RES;		// WizOn=1, LATCH=0, CS=0, Rd=1, Wr=1, /RES=1
}


/***********************
 * DS customized I/O  Function *
 ***********************/
 
void     setMR(uint16 val)
{
  //IINCHIP_CRITICAL_SECTION_ENTER();
  
	//WizWrR0 (MR0, (U8)(data>>8));
	FIO1PINU  = W530_MR0a | LATCH_STRBa; // WLD Edge, Wr-0						
	FIO1PINU  = ((val&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	asm volatile ("nop");
	asm volatile ("nop");
	asm volatile ("nop");
	
	asm volatile ("nop");
	asm volatile ("nop");
	
	FIO1CLRU = WIZ_CSa;
	FIO1PINU  = W530_MR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 			
	
	//WizWrR1 (MR1, (U8)(val));
	FIO1PINU  = W530_MR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	FIO1PINU  = (val&0x00ff) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	asm volatile ("nop");
	asm volatile ("nop");
	asm volatile ("nop");
	
	asm volatile ("nop");
	asm volatile ("nop");
	
	FIO1CLRU = WIZ_CSa;
	FIO1PINU  = W530_MR1IDLEa; // WLD-transparent Wr-1, CS-inactive 	
      
  //IINCHIP_CRITICAL_SECTION_EXIT();
	
}


uint16   getMR(void)
{
	uint16 val;
	uint8 v1, v2;
	
  //IINCHIP_CRITICAL_SECTION_ENTER();
  
	//WizRdR0 (MR0, (U8)(val>>8));
	FIO1PINU  = R530_MR0a | LATCH_STRBa;	// WLD Edge, Rd-0
  FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
	FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
	asm volatile ("nop");			// Must be 3 NOPs here
	asm volatile ("nop");
	asm volatile ("nop");
	asm volatile ("nop");
	v1 = FIO1PIN2;
	asm volatile ("nop");
		
	FIO1PINU  = R530_MR0IDLEa | LATCH_STRBa;	// WLD Edge, Rd-1, CS-inactive 		
  FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
  FIO1CLR3 = LATCH_STRBb;
	
	//WizRdR1 (MR1, (U8)(val));
	FIO1PINU  = R530_MR1a | LATCH_STRBa;	// WLD Edge, Rd-0
  FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
	FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
	asm volatile ("nop");			// Must be 3 NOPs here
	asm volatile ("nop");
	asm volatile ("nop");
	asm volatile ("nop");
	v2 = FIO1PIN2;
  
	FIO1PINU  = R530_MR1IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
  FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
  FIO1CLR3 = LATCH_STRBb;
  val = (v1<<8)|v2;
     
  //IINCHIP_CRITICAL_SECTION_EXIT();
  
	return val;
}

void  iinchip_init(void)
{
	setMR( MR_RST );
	delay(2000000);				// wait 200msec 
	setMR( MR_IND );

}

 
uint16  IINCHIP_READ(uint32 addr)
{
	uint16 val;

  //IINCHIP_CRITICAL_SECTION_ENTER();
  
	//WizWrR0 (IDM_AR0, (U8)(Addr>>8));
	FIO1PINU  = W530_AR0a | LATCH_STRBa; // WLD Edge, Wr-0				
	FIO1PINU  = ((addr&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	NOP_2					
	FIO1PINU  = W530_AR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 		
	
	//WizWrR0 (IDM_AR1, (U8)(Addr));
	FIO1PINU  = W530_AR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	FIO1PINU  = (addr&0x00ff) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	NOP_2					
	FIO1PINU  = W530_AR1IDLEa;	// WLD-transparent Wr-1, CS-inactive 		

	//WizRdR0 (IDM_DR0, (U8)(val>>8));
	FIO1PINU  = R530_DR0a | LATCH_STRBa;	// WLD Edge, Rd-0	
  FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
	FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
	NOP_3					// Must be 3 NOPs here
	val = FIO1PIN2<<8;

	FIO1PINU  = R530_DR0IDLEa | LATCH_STRBa;	// WLD Edge, Rd-1, CS-inactive 		
  FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
  FIO1CLR3 = LATCH_STRBb;
	
	//WizRdR1 (IDM_DR1, (U8)(val));
	FIO1PINU  = R530_DR1a | LATCH_STRBa;	// WLD Edge, Rd-0
  FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
	FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
	NOP_3					// Must be 3 NOPs here
	val |= FIO1PIN2;
		
	FIO1PINU  = R530_DR1IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
  FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
  FIO1CLR3 = LATCH_STRBb;
    
  //IINCHIP_CRITICAL_SECTION_EXIT();
  
	return val;
}

void  IINCHIP_WRITE(uint32 addr,uint16 data)
{
  //IINCHIP_CRITICAL_SECTION_ENTER();
  
	//WR5300_AR0	= (IDM_AR0_<<16)|WIZ_RD|WIZ_RES|WIZ_ON|LATCH_STRB
	FIO1PINU  = W530_AR0a | LATCH_STRBa; // WLD Edge, Wr-0				
	FIO1PINU  = ((addr&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	NOP_2					
	FIO1PINU  = W530_AR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 		
	
	//WizWrR0 (IDM_AR1, (U8)(Addr));
	FIO1PINU  = W530_AR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	FIO1PINU  = (addr&0x00ff) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	NOP_2					
	FIO1PINU  = W530_AR1IDLEa;	// WLD-transparent Wr-1, CS-inactive 		
	
	//WizWrR0 (IDM_DR0, (U8)(val>>8));
	FIO1PINU  = W530_DR0a | LATCH_STRBa; // WLD Edge, Wr-0						
	FIO1PINU  = ((data&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	NOP_2					
	FIO1PINU  = W530_DR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 			
	
	//WizWrR1 (IDM_DR1, (U8)(val));
	FIO1PINU  = W530_DR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	FIO1PINU  = (data&0x00ff) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	NOP_2					
	FIO1PINU  = W530_DR1IDLEa; // WLD-transparent Wr-1, CS-inactive 
		
  //IINCHIP_CRITICAL_SECTION_EXIT();

}


uint32   wiz_write_buf(SOCKET s, uint8* buf, uint32 len)
{
  uint32 idx=0;
  uint16 addr;
  uint8	 data;
  int	tcnt;
  
  //IINCHIP_CRITICAL_SECTION_ENTER();
  
  addr = Sn_TX_FIFOR(s);
  
  //WizWrR0 (IDM_AR0, (U8)(Addr>>8));
	FIO1PINU  = W530_AR0a | LATCH_STRBa; // WLD Edge, Wr-0				
	FIO1PINU  = ((addr&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	NOP_2					
	FIO1PINU  = W530_AR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 	
	
	//WizWrR0 (IDM_AR1, (U8)(Addr));
	FIO1PINU  = W530_AR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	FIO1PINU  = (addr&0x00ff) | WIZ_CSa | LATCH_STRBa;; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	NOP_2					
	FIO1PINU  = W530_AR1IDLEa;	// WLD-transparent Wr-1, CS-inactive 		
  
  idx = 0;
  data = *(buf+idx);
	// For speed purpose write linear block 4-byte long
	if ( len > 4 )	{
		tcnt = len >> 2;	// len/4
	  while ( tcnt>0 ) {
			//WizWrR0 (IDM_DR0, (U8)(data>>8));
			FIO1PINU  = W530_DR0a | LATCH_STRBa; // WLD Edge, Wr-0						
			FIO1PINU  =  data | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
			idx++;
			data = *(buf+idx);
			FIO1PINU  = W530_DR0IDLEa;	// WLD-transparent Wr-1, CS-inactive
		
			//WizWrR1 (IDM_DR1, (U8)(data));
			FIO1PINU  = W530_DR1a | LATCH_STRBa; // WLD Edge, Wr-0						
			FIO1PINU  = data | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
			idx++;
			data = *(buf+idx);
			FIO1PINU  = W530_DR1IDLEa; // WLD-transparent Wr-1, CS-inactive 
				
			//WizWrR0 (IDM_DR0, (U8)(data>>8));
			FIO1PINU  = W530_DR0a | LATCH_STRBa; // WLD Edge, Wr-0						
			FIO1PINU  =  data | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
			idx++;
			data = *(buf+idx);
			FIO1PINU  = W530_DR0IDLEa;	// WLD-transparent Wr-1, CS-inactive
		
			//WizWrR1 (IDM_DR1, (U8)(data));
			FIO1PINU  = W530_DR1a | LATCH_STRBa; // WLD Edge, Wr-0						
			FIO1PINU  = data | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
			idx++;
			data = *(buf+idx);
			FIO1PINU  = W530_DR1IDLEa; // WLD-transparent Wr-1, CS-inactive 
			
			tcnt--;	
		}
	}
  
  while ( idx < len ) {
		//WizWrR0 (IDM_DR0, (U8)(data>>8));
		FIO1PINU  = W530_DR0a | LATCH_STRBa; // WLD Edge, Wr-0						
		FIO1PINU  =  data | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
		idx++;
		data = *(buf+idx);
		FIO1PINU  = W530_DR0IDLEa;	// WLD-transparent Wr-1, CS-inactive
		
		//WizWrR1 (IDM_DR1, (U8)(data));
		FIO1PINU  = W530_DR1a | LATCH_STRBa; // WLD Edge, Wr-0						
		FIO1PINU  = data | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
		idx++;
		data = *(buf+idx);
		FIO1PINU  = W530_DR1IDLEa; // WLD-transparent Wr-1, CS-inactive 	
	}
  //IINCHIP_CRITICAL_SECTION_EXIT();
	
  return len;   

}


uint32   wiz_read_buf(SOCKET s, uint8* buf, uint32 len)
{
  uint32 idx=0;
  uint16 addr;
  int	tcnt;
  
  addr = Sn_RX_FIFOR(s);		// Socket(s) RX_FIFO_REG addr
  
  //WizWrR0 (IDM_AR0, (U8)(Addr>>8));
	FIO1PINU  = W530_AR0a | LATCH_STRBa; // WLD Edge, Wr-0				
	FIO1PINU  = ((addr&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	NOP_2					
	FIO1PINU  = W530_AR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 	
	
	//WizWrR0 (IDM_AR1, (U8)(Addr));
	FIO1PINU  = W530_AR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	FIO1PINU  = (addr&0x00ff) | WIZ_CSa | LATCH_STRBa;; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	NOP_2					
	FIO1PINU  = W530_AR1IDLEa;	// WLD-transparent Wr-1, CS-inactive 
	
	idx = 0;
	// For speed purpose read linear block 8-byte long
	if ( len > 8 )	{
		tcnt = len >> 3;	// len/8
	  while ( tcnt>0 ) {
   		//WizRdR0 (IDM_DR0, (U8)(val>>8));
			FIO1PINU  = R530_DR0a | LATCH_STRBa;	// WLD Edge, Rd-0	
  		FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
			FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
			NOP_3					// Must be 3 NOPs here
			*((uint8*)(buf+idx)) = FIO1PIN2;
		
			FIO1PINU  = R530_DR0IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
	  	FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
	  	FIO1CLR3 = LATCH_STRBb;
		
			//WizRdR1 (IDM_DR1, (U8)(val));
			FIO1PINU  = R530_DR1a | LATCH_STRBa;	// WLD Edge, Rd-0
  		FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
			FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
			NOP_3					// Must be 3 NOPs here
			*((uint8*)(buf+idx+1)) = FIO1PIN2;
		
			FIO1PINU  = R530_DR1IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
	  	FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
	  	FIO1CLR3 = LATCH_STRBb;

   		//WizRdR0 (IDM_DR0, (U8)(val>>8));
			FIO1PINU  = R530_DR0a | LATCH_STRBa;	// WLD Edge, Rd-0	
  		FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
			FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
			NOP_3					// Must be 3 NOPs here
			*((uint8*)(buf+idx+2)) = FIO1PIN2;
		
			FIO1PINU  = R530_DR0IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
	  	FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
	  	FIO1CLR3 = LATCH_STRBb;
		
			//WizRdR1 (IDM_DR1, (U8)(val));
			FIO1PINU  = R530_DR1a | LATCH_STRBa;	// WLD Edge, Rd-0
  		FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
			FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
			NOP_3					// Must be 3 NOPs here
			*((uint8*)(buf+idx+3)) = FIO1PIN2;
		
			FIO1PINU  = R530_DR1IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
	  	FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
	  	FIO1CLR3 = LATCH_STRBb;
	  	
   		//WizRdR0 (IDM_DR0, (U8)(val>>8));
			FIO1PINU  = R530_DR0a | LATCH_STRBa;	// WLD Edge, Rd-0	
  		FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
			FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
			NOP_3					// Must be 3 NOPs here
			//asm volatile ("nop");
			*((uint8*)(buf+idx+4)) = FIO1PIN2;
		
			FIO1PINU  = R530_DR0IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
	  	FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
	  	FIO1CLR3 = LATCH_STRBb;
		
			//WizRdR1 (IDM_DR1, (U8)(val));
			FIO1PINU  = R530_DR1a | LATCH_STRBa;	// WLD Edge, Rd-0
  		FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
			FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
			NOP_3					// Must be 3 NOPs here
			*((uint8*)(buf+idx+5)) = FIO1PIN2;
		
			FIO1PINU  = R530_DR1IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
	  	FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
	  	FIO1CLR3 = LATCH_STRBb;

   		//WizRdR0 (IDM_DR0, (U8)(val>>8));
			FIO1PINU  = R530_DR0a | LATCH_STRBa;	// WLD Edge, Rd-0	
  		FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
			FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
			NOP_3					// Must be 3 NOPs here
			*((uint8*)(buf+idx+6)) = FIO1PIN2;
		
			FIO1PINU  = R530_DR0IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
	  	FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
	  	FIO1CLR3 = LATCH_STRBb;
		
			//WizRdR1 (IDM_DR1, (U8)(val));
			FIO1PINU  = R530_DR1a | LATCH_STRBa;	// WLD Edge, Rd-0
  		FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
			FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
			asm volatile ("nop");			// Must be 3 instrustions here
			tcnt--;
			asm volatile ("nop");
			*((uint8*)(buf+idx+7)) = FIO1PIN2;
		
			FIO1PINU  = R530_DR1IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
	  	FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
	  	FIO1CLR3 = LATCH_STRBb;
	  	
			idx += 8;

		}
	}

  while ( idx < len ) {
   	//WizRdR0 (IDM_DR0, (U8)(val>>8));
		FIO1PINU  = R530_DR0a | LATCH_STRBa;	// WLD Edge, Rd-0	
  	FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
		FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
		NOP_3					// Must be 3 NOPs here
		*((uint8*)(buf+idx)) = FIO1PIN2;
		
		FIO1PINU  = R530_DR0IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
	  FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
	  FIO1CLR3 = LATCH_STRBb;
  	idx++;
		
		//WizRdR1 (IDM_DR1, (U8)(val));
		FIO1PINU  = R530_DR1a | LATCH_STRBa;	// WLD Edge, Rd-0
  	FIO1DIR2  = 0x00;				// P1.16 .. P1.23 Input
		FIO1PIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
		NOP_3					// Must be 3 NOPs here
		*((uint8*)(buf+idx)) = FIO1PIN2;
		
		FIO1PINU  = R530_DR1IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
	  FIO1DIR2  = 0xFF;				// P1.16 .. P1.23 Output
	  FIO1CLR3 = LATCH_STRBb;
  	idx++;
	}	
			
  //IINCHIP_CRITICAL_SECTION_EXIT();
	
  return len;
}

void W5300PwrOn(void)
{
  FIO1PIN    = WIZ_ON|WIZ_RD|WIZ_WR|WIZ_RES;		// WizOn=1, LATCH=0, CS=0, Rd=1, Wr=1, /RES=1
  delay(2000000);
  
  // Activate WIZ_RESET
	FIO1CLR    = WIZ_RES;	  
  delay(50);
	FIO1SET    = WIZ_RES;	  
  delay(200000);
}

void W5300PwrOff(void)
{
	// Set all W5300 signals at "0"
  FIO1CLR3 = LATCH_STRBb;			// Latch Transparent
  delay(100);
  FIO1CLR  = WIZ_A0|WIZ_A1|WIZ_A2|WIZ_RD|WIZ_WR|WIZ_RES;
  delay(100);
  FIO1SET3 = WIZ_CSb;
  delay(100);
  
	FIO1CLR  = WIZ_ON;		// WizOn=0
  delay(100);
}

void W5300Init2(void)
{
	int i;
	
  CRdyMax = 0;
  
	for (i = 0; i < MAX_SOCK_NUM; i++) {
		// Enable	only SENDOK & TIMEOUT Ints
		setSn_IMR(i, 0x10);
		
		ssrErr[i] = 0;
		EstbPhase[i] = 0;
	}	
}

int Rd5300_bl(uint16 addr, uint8* buf, int len)
{
  int idx = 0;
  uint16 v;

  for (idx = 0; idx < len; idx++ ) {
	  v = IINCHIP_READ( addr );
	  *((uint8*)(buf+idx)) = (v&0xff00)>>8;
	  idx++;
		*((uint8*)(buf+idx)) = v&0xff;
  	addr += 2;
	}
	return len;
}

