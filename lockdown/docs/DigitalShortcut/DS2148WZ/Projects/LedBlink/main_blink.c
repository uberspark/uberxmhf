/** @file
  main program
  Project Includes:
  	LedBlink on P1.24 - Morse Code 
 		Serial Terminal Communication 115200kbd
 		Printf on Serial Console
 		Micro Command Interpretter 
 		Loop Toggle P0.5 Pin
 		1sec Heart Beat
 Copyright Digital Shortcut 2008 **/


#include "console.h"

#include "lpc21xx.h"
#include "timerC.h"          	// timer functions

#define LF	10
#define CR	13

#define BAUD_RATE	115200

#define STAR_INTERVAL 1000		// in miliseconds


unsigned int	Event;
int		miliSec;
int		CmdLen;

char	CmdStr[30], cmd;

// external prototypes
extern	int printf(const char *format, ...);
extern	int sprintf(char *out, const char *format, ...);
extern	void Init2148(void);

// Forward Prototypes
void 	InitP0(void);
void 	InitP1(void);
void 	ToggleP0_5(void);
void 	ToggleP0_4(void);
void 	InitLed(void);
void 	BlinkLed(void);
int		GetCmdLine(void);



void InitP0(void)
{
  // Initialize P0.7 .. P0.0
  PINSEL0   &= 0x000000FF;		// P0.7 .. P0.0 GPIOs
  FIO0DIR   |= 0x000000FF;		// P0.7 .. P0.0 Output
  FIO0SET    = 0x000000FF;		// "1" on P0.0.. P0.7
}    

void InitP1(void)
{
  // Initialize P1.16 .. P1.32
  // P1.16-P1.24:GPIO or ETM Port, P1.24:GPIO, P1.26-P1.31: GPIO or JTAG Port
  
  PINSEL2    = 0x4;						// P1.16 .. P1.25 GPIOs, P1.26..P1.31 Jtag port
  FIO1DIR    = 0x03FF0000;		// P1.16 .. P1.25 Output
  FIO1SET    = 0x000000FF;
}

void ToggleP0_5(void)
{
	if ( FIO0PIN & 0x00000020 ) 
		FIO0CLR = 0x00000020;    			//P0.5 = 0 
	else 	FIO0SET = 0x00000020;			//P0.5 = 1
}

void ToggleP0_4(void)
{
	if ( FIO0PIN & 0x00000010 ) 
		FIO0CLR = 0x00000010;    			//P0.4 = 0 
	else 	FIO0SET = 0x00000010;			//P0.4 = 1
}

int LedCnt, SeqCnt;

//Led Blink sequence: msecOn, msecOff, msecOn, msecOff,....
//int LedSeq[] 			= { 400, 200, 400, 200, 50, 50, 50, 50, 50, 50, 50, 1500};
#define DOT			50, 50
#define DASH		500, 200
#define FIN			50, 1500

int LedSeq[] 			= { DASH, DASH, DOT, DOT, DOT, FIN};

void InitLed(void)
{
	FIO1CLR = 0x01000000;			//P1.24 = 1
	LedCnt = 2;
	SeqCnt = 0;
}

void BlinkLed(void)
{
	if ( (LedCnt--)==0 ) {
		LedCnt = LedSeq[SeqCnt];
		if ( ++SeqCnt >= (int)(sizeof LedSeq/sizeof LedSeq[0]) ) SeqCnt = 0;
		
		if ( FIO1PIN & 0x01000000 )  
			FIO1CLR = 0x01000000;    	//P1.24 = 0 
		else 	
			FIO1SET = 0x01000000;			//P1.24 = 1
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
	return CRdy;
}
 
/*************************************************************************
	main
	====
**************************************************************************/
int main(void)
{
	// PLL and MAM
	Init2148();

	// init console Baud Rate 115200kbd
	ConsoleInit(60000000 / (16 * BAUD_RATE));
	
	printf("### Blink Led (Morse) 1/29/09 ###\n");
	
	timerInit();
	
	InitP0();
	InitP1();
	InitLed();
	
	Event = 0;
	miliSec = 0;
	CmdLen = 0;
	
	while (1) {
		ToggleP0_4();
		
		if ( GetCmdLine()&&(CmdLen>0) ) {
			cmd = CmdStr[0];
      if ( (cmd>0x60)&&(cmd<0x7B) ) {
				cmd = cmd - 0x20;		// ASCII toupper
			}
			      
      switch (cmd) {
			case 'L':
				// Loop 
				printf("***Loop... Press any Key to Abort\n");
				while (1) {
					ToggleP0_5();
					if ( my_getchar()!= EOF ) break;
				}
				break;				
							
			case 'I':
				// INFO
				printf("**Info 2345***\n");
				break;

			default:
				printf("*CmdErr\n");
				break;
			}
			CmdLen = 0;						
		}												
		
		if ( Event ) {
			miliSec++;
			Event = 0;
			
			BlinkLed();
			if ( (miliSec>=STAR_INTERVAL)&&(CmdLen==0) ) {
				printf("*");
				miliSec = 0;
			}
		}
	}
	
	return 0;
}
