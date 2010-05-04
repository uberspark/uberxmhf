/** file ds5300.c
 * Implementation of Digital Shortcut customized W5300 I/O fucntions for DS2148WZ board
 *
 * Copyright Digital Shortcut Inc. (BSD licence) 2009 **/
 
#include "FreeRTOS.h"
#include "task.h"

 
#include	"w5300.h"
#include	"ds5300.h"
#include	"../digi_short/wiz_ds.h"


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


extern 	int 		W53IntCnt, SpurIntCnt, CRdyMax;

extern	int			W53ErFlg, MarkrIdx, IntLev;
extern	uint16	DB_MarkerL;
extern	uint16	MarkrBuf[];

extern	uint8		EstbPhase[];
extern 	int			ssrErr[];

extern	void	delay(unsigned long d);
extern	void	LogWr(uint16 data);
extern	void	LogWrTim( void );

int printf(const char *format, ...);

uint8 SpurInt[MAX_SOCK_NUM];


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


/***********************
 * DS customized I/O  Function *
 ***********************/
 
void     setMR(uint16 val)
{
  //IINCHIP_CRITICAL_SECTION_ENTER();
  
	//WizWrR0 (MR0, (U8)(data>>8));
	GPIO1_FIOPINH  = W530_MR0a | LATCH_STRBa; // WLD Edge, Wr-0						
	GPIO1_FIOPINH  = ((val&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	asm volatile ("nop");
	asm volatile ("nop");
	asm volatile ("nop");
	
	asm volatile ("nop");
	asm volatile ("nop");
	
	GPIO1_FIOCLRH = WIZ_CSa;
	GPIO1_FIOPINH  = W530_MR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 			
	
	//WizWrR1 (MR1, (U8)(val));
	GPIO1_FIOPINH  = W530_MR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	GPIO1_FIOPINH  = (val&0x00ff) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	asm volatile ("nop");
	asm volatile ("nop");
	asm volatile ("nop");
	
	asm volatile ("nop");
	asm volatile ("nop");
	
	GPIO1_FIOCLRH = WIZ_CSa;
	GPIO1_FIOPINH  = W530_MR1IDLEa; // WLD-transparent Wr-1, CS-inactive 	
      
  //IINCHIP_CRITICAL_SECTION_EXIT();
	
}


uint16   getMR(void)
{
	uint16 val;
	uint8 v1, v2;
	
  //IINCHIP_CRITICAL_SECTION_ENTER();

	//WizRdR0 (MR0, (U8)(val>>8));
	GPIO1_FIOPINH  = R530_MR0a | LATCH_STRBa;	// WLD Edge, Rd-0
  GPIO1_FIODIR2  = 0x00;				// P1.16 .. P1.23 Input
	GPIO1_FIOPIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
	asm volatile ("nop");			// Must be 3 NOPs here
	asm volatile ("nop");
	asm volatile ("nop");
	asm volatile ("nop");
	v1 = GPIO1_FIOPIN2;
	asm volatile ("nop");
		
	GPIO1_FIOPINH  = R530_MR0IDLEa | LATCH_STRBa;	// WLD Edge, Rd-1, CS-inactive 		
  GPIO1_FIODIR2  = 0xFF;				// P1.16 .. P1.23 Output
  GPIO1_FIOCLR3 = LATCH_STRBb;
	
	//WizRdR1 (MR1, (U8)(val));
	GPIO1_FIOPINH  = R530_MR1a | LATCH_STRBa;	// WLD Edge, Rd-0
  GPIO1_FIODIR2  = 0x00;				// P1.16 .. P1.23 Input
	GPIO1_FIOPIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
	asm volatile ("nop");			// Must be 3 NOPs here
	asm volatile ("nop");
	asm volatile ("nop");
	asm volatile ("nop");
	v2 = GPIO1_FIOPIN2;
  
	GPIO1_FIOPINH  = R530_MR1IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
  GPIO1_FIODIR2  = 0xFF;				// P1.16 .. P1.23 Output
  GPIO1_FIOCLR3 = LATCH_STRBb;
  val = (v1<<8)|v2;
     
  //IINCHIP_CRITICAL_SECTION_EXIT();
  
	return val;
}


void  iinchip_init(void)
{
	setMR( MR_RST ); 		//setMR( 0x0080 );
	delay(2000000);			// wait 200msec 
	setMR( MR_IND );		//setMR( 0x0001 );

}

 
uint16  IINCHIP_READ(uint32 addr)
{
	uint16 val;

  //IINCHIP_CRITICAL_SECTION_ENTER();
  
	//WizWrR0 (IDM_AR0, (U8)(Addr>>8));
	GPIO1_FIOPINH  = W530_AR0a | LATCH_STRBa; // WLD Edge, Wr-0				
	GPIO1_FIOPINH  = ((addr&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	asm volatile ("nop");
	asm volatile ("nop");
	GPIO1_FIOPINH  = W530_AR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 		
	
	//WizWrR0 (IDM_AR1, (U8)(Addr));
	GPIO1_FIOPINH  = W530_AR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	GPIO1_FIOPINH  = (addr&0x00ff) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	asm volatile ("nop");
	asm volatile ("nop");
	GPIO1_FIOPINH  = W530_AR1IDLEa;	// WLD-transparent Wr-1, CS-inactive 		

	//WizRdR0 (IDM_DR0, (U8)(val>>8));
	GPIO1_FIOPINH  = R530_DR0a | LATCH_STRBa;	// WLD Edge, Rd-0	
  GPIO1_FIODIR2  = 0x00;				// P1.16 .. P1.23 Input
	GPIO1_FIOPIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
	asm volatile ("nop");			// Must be 3 NOPs here
	asm volatile ("nop");
	asm volatile ("nop");
	val = GPIO1_FIOPIN2<<8;

	GPIO1_FIOPINH  = R530_DR0IDLEa | LATCH_STRBa;	// WLD Edge, Rd-1, CS-inactive 		
  GPIO1_FIODIR2  = 0xFF;				// P1.16 .. P1.23 Output
  GPIO1_FIOCLR3 = LATCH_STRBb;
	
	//WizRdR1 (IDM_DR1, (U8)(val));
	GPIO1_FIOPINH  = R530_DR1a | LATCH_STRBa;	// WLD Edge, Rd-0
  GPIO1_FIODIR2  = 0x00;				// P1.16 .. P1.23 Input
	GPIO1_FIOPIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
	asm volatile ("nop");			// Must be 3 NOPs here
	asm volatile ("nop");
	asm volatile ("nop");
	val |= GPIO1_FIOPIN2;
		
	GPIO1_FIOPINH  = R530_DR1IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
  GPIO1_FIODIR2  = 0xFF;				// P1.16 .. P1.23 Output
  GPIO1_FIOCLR3 = LATCH_STRBb;
   
  //IINCHIP_CRITICAL_SECTION_EXIT();
  
	return val;
}

void  IINCHIP_WRITE(uint32 addr,uint16 data)
{
	
  //IINCHIP_CRITICAL_SECTION_ENTER();
  
	//WR5300_AR0	= (IDM_AR0_<<16)|WIZ_RD|WIZ_RES|WIZ_ON|LATCH_STRB
	GPIO1_FIOPINH  = W530_AR0a | LATCH_STRBa; // WLD Edge, Wr-0				
	GPIO1_FIOPINH  = ((addr&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	asm volatile ("nop");
	asm volatile ("nop");
	GPIO1_FIOPINH  = W530_AR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 		
	
	//WizWrR0 (IDM_AR1, (U8)(Addr));
	GPIO1_FIOPINH  = W530_AR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	GPIO1_FIOPINH  = (addr&0x00ff) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	asm volatile ("nop");
	asm volatile ("nop");
	GPIO1_FIOPINH  = W530_AR1IDLEa;	// WLD-transparent Wr-1, CS-inactive 		
	
	//WizWrR0 (IDM_DR0, (U8)(val>>8));
	GPIO1_FIOPINH  = W530_DR0a | LATCH_STRBa; // WLD Edge, Wr-0						
	GPIO1_FIOPINH  = ((data&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	asm volatile ("nop");
	asm volatile ("nop");
	GPIO1_FIOPINH  = W530_DR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 			
	
	//WizWrR1 (IDM_DR1, (U8)(val));
	GPIO1_FIOPINH  = W530_DR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	GPIO1_FIOPINH  = (data&0x00ff) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	asm volatile ("nop");
	asm volatile ("nop");
	GPIO1_FIOPINH  = W530_DR1IDLEa; // WLD-transparent Wr-1, CS-inactive 
		
  //IINCHIP_CRITICAL_SECTION_EXIT();

}


uint32   wiz_write_buf(SOCKET s, uint8* buf, uint32 len)
{
  uint32 idx=0;
  uint16 addr;
  uint8	 data;
  
  //IINCHIP_CRITICAL_SECTION_ENTER();
  
  addr = Sn_TX_FIFOR(s);
  
  //WizWrR0 (IDM_AR0, (U8)(Addr>>8));
	GPIO1_FIOPINH  = W530_AR0a | LATCH_STRBa; // WLD Edge, Wr-0				
	GPIO1_FIOPINH  = ((addr&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	asm volatile ("nop");
	asm volatile ("nop");
	GPIO1_FIOPINH  = W530_AR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 	
	
	//WizWrR0 (IDM_AR1, (U8)(Addr));
	GPIO1_FIOPINH  = W530_AR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	GPIO1_FIOPINH  = (addr&0x00ff) | WIZ_CSa | LATCH_STRBa;; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	asm volatile ("nop");
	asm volatile ("nop");
	GPIO1_FIOPINH  = W530_AR1IDLEa;	// WLD-transparent Wr-1, CS-inactive 		
  
  idx = 0;
  data = *(buf+idx);
  while ( idx < len ) {
		//WizWrR0 (IDM_DR0, (U8)(data>>8));
		GPIO1_FIOPINH  = W530_DR0a | LATCH_STRBa; // WLD Edge, Wr-0						
		GPIO1_FIOPINH  =  data | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
		idx++;
		data = *(buf+idx);
		GPIO1_FIOPINH  = W530_DR0IDLEa;	// WLD-transparent Wr-1, CS-inactive
		
		//WizWrR1 (IDM_DR1, (U8)(val));
		GPIO1_FIOPINH  = W530_DR1a | LATCH_STRBa; // WLD Edge, Wr-0						
		GPIO1_FIOPINH  = data | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
		idx++;
		data = *(buf+idx);
		GPIO1_FIOPINH  = W530_DR1IDLEa; // WLD-transparent Wr-1, CS-inactive 	
	}
    
  //IINCHIP_CRITICAL_SECTION_EXIT();
	
  return len;   
}

void   wiz_write_test(uint16 addr, uint8* buf, int len)
{
  int idx;
  uint8	 data;
  
  //IINCHIP_CRITICAL_SECTION_ENTER();
  
  //WizWrR0 (IDM_AR0, (U8)(Addr>>8));
	GPIO1_FIOPINH  = W530_AR0a | LATCH_STRBa; // WLD Edge, Wr-0				
	GPIO1_FIOPINH  = ((addr&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	asm volatile ("nop");
	asm volatile ("nop");
	GPIO1_FIOPINH  = W530_AR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 	
	
	//WizWrR0 (IDM_AR1, (U8)(Addr));
	GPIO1_FIOPINH  = W530_AR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	GPIO1_FIOPINH  = (addr&0x00ff) | WIZ_CSa | LATCH_STRBa;; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	asm volatile ("nop");
	asm volatile ("nop");
	GPIO1_FIOPINH  = W530_AR1IDLEa;	// WLD-transparent Wr-1, CS-inactive 

  idx = 0;
  data = *(buf+idx);
	
  //for (idx = 0; idx < len; ) {
  while ( idx < len ) {
		//WizWrR0 (IDM_DR0, (U8)(data>>8));
		GPIO1_FIOPINH  = W530_DR0a | LATCH_STRBa; // WLD Edge, Wr-0						
		GPIO1_FIOPINH  =  data | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
		// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
		//asm volatile ("nop");
		//asm volatile ("nop");
		idx++;
		data = *(buf+idx);
		GPIO1_FIOPINH  = W530_DR0IDLEa;	// WLD-transparent Wr-1, CS-inactive
		
		//WizWrR1 (IDM_DR1, (U8)(val));
		GPIO1_FIOPINH  = W530_DR1a | LATCH_STRBa; // WLD Edge, Wr-0						
		GPIO1_FIOPINH  = data | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
		idx++;
		data = *(buf+idx);
		GPIO1_FIOPINH  = W530_DR1IDLEa; // WLD-transparent Wr-1, CS-inactive 	
	}
    
  //IINCHIP_CRITICAL_SECTION_EXIT();
}


uint32   wiz_read_buf(SOCKET s, uint8* buf, uint32 len)
{
  uint32 idx=0;
  uint16 addr;
  
  addr = Sn_RX_FIFOR(s);
  
  //WizWrR0 (IDM_AR0, (U8)(Addr>>8));
	GPIO1_FIOPINH  = W530_AR0a | LATCH_STRBa; // WLD Edge, Wr-0				
	GPIO1_FIOPINH  = ((addr&0xff00)>>8) | WIZ_CSa | LATCH_STRBa; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	asm volatile ("nop");
	asm volatile ("nop");
	GPIO1_FIOPINH  = W530_AR0IDLEa;	// WLD-transparent Wr-1, CS-inactive 	
	
	//WizWrR0 (IDM_AR1, (U8)(Addr));
	GPIO1_FIOPINH  = W530_AR1a | LATCH_STRBa; // WLD Edge, Wr-0						
	GPIO1_FIOPINH  = (addr&0x00ff) | WIZ_CSa | LATCH_STRBa;; // CS-active, WLD-locked
	// 2 NOPs here assures min 50ns CS (with LPC2148 run on 60MHz)
	asm volatile ("nop");
	asm volatile ("nop");
	GPIO1_FIOPINH  = W530_AR1IDLEa;	// WLD-transparent Wr-1, CS-inactive 
			
  for (idx = 0; idx < len; idx++) {
   	//WizRdR0 (IDM_DR0, (U8)(val>>8));
		GPIO1_FIOPINH  = R530_DR0a | LATCH_STRBa;	// WLD Edge, Rd-0	
  	GPIO1_FIODIR2  = 0x00;				// P1.16 .. P1.23 Input
		GPIO1_FIOPIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
		asm volatile ("nop");			// Must be 3 NOPs here
		asm volatile ("nop");
		asm volatile ("nop");
		*((uint8*)(buf+idx)) = GPIO1_FIOPIN2;
		
		GPIO1_FIOPINH  = R530_DR0IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
	  GPIO1_FIODIR2  = 0xFF;				// P1.16 .. P1.23 Output
	  GPIO1_FIOCLR3 = LATCH_STRBb;
  	idx++;
		
		//WizRdR1 (IDM_DR1, (U8)(val));
		GPIO1_FIOPINH  = R530_DR1a | LATCH_STRBa;	// WLD Edge, Rd-0
  	GPIO1_FIODIR2  = 0x00;				// P1.16 .. P1.23 Input
		GPIO1_FIOPIN3  = WIZ_CSb | LATCH_STRBb; // CS-active, WLD-locked
		asm volatile ("nop");			// Must be 3 NOPs here
		asm volatile ("nop");
		asm volatile ("nop");
		*((uint8*)(buf+idx)) = GPIO1_FIOPIN2;
		
		GPIO1_FIOPINH  = R530_DR1IDLEa | LATCH_STRBa;	// WLD-transparent Rd-1, CS-inactive 		
	  GPIO1_FIODIR2  = 0xFF;				// P1.16 .. P1.23 Output
	  GPIO1_FIOCLR3 = LATCH_STRBb;
		
	}	
  //IINCHIP_CRITICAL_SECTION_EXIT();
	
  return len;
}


void SpuriousW5300Int(void) __attribute__((naked));
void SpuriousW5300Int(void)
{
	int i;
	volatile uint8 v1;
	
	portSAVE_CONTEXT();

	LogWr(0x47); LogWr(IINCHIP_READ(IR)); 

	SpurIntCnt++;
	for(i = 0 ; i < MAX_SOCK_NUM ; i++) {
		v1 = (uint8)IINCHIP_READ(Sn_IR(i));
		SpurInt[i] = v1;
		if ( v1 != 0 ) {
			LogWr(0x48); LogWr(i); LogWr(v1);
			IINCHIP_WRITE(Sn_IR(i), v1);
		}
	}
	
	IINCHIP_WRITE(IR, 0xFF00);
		
  SCB_EXTINT  |= SCB_EXTINT_EINT0;
	
	VIC_SoftIntClear = (1<<VIC_Channel_EINT0);
	VIC_VectAddr = 0x00000000;             // clear this interrupt from the VIC
	
	portRESTORE_CONTEXT();
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

