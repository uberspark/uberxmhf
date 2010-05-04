/*
	LPCUSB, an USB device driver for LPC microcontrollers	
	Copyright (C) 2006 Bertrik Sikken (bertrik@sikken.nl)

	Redistribution and use in source and binary forms, with or without
	modification, are permitted provided that the following conditions are met:

	1. Redistributions of source code must retain the above copyright
	   notice, this list of conditions and the following disclaimer.
	2. Redistributions in binary form must reproduce the above copyright
	   notice, this list of conditions and the following disclaimer in the
	   documentation and/or other materials provided with the distribution.
	3. The name of the author may not be used to endorse or promote products
	   derived from this software without specific prior written permission.

	THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
	IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
	OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
	IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, 
	INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
	NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
	DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
	THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
	(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
	THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

/*
	Simple console input/output, over serial port #0

	Partially copied from Jim Lynch's tutorial
*/

#include "../ARM2148/lpc21xx.h"
#include "console.h"
#include "../ARM2148/processor.h"


extern	void	delay(unsigned long d);

int my_putchar(int ch);  


#define	sOBUF_SIZE	400
char		sOutBuf[sOBUF_SIZE];
volatile	char* 	sOutWrPtr;
volatile	char* 	sOutRdPtr;
volatile	int		sOutFull;
volatile	int		OutHCnt;	


void Uart0ISR(void) __attribute__((naked));
void Uart0ISR(void)
{
	char ch;
	
	ISR_ENTRY();

	if ( (sOutWrPtr != sOutRdPtr)||(sOutFull==1) ) {	
		ch = *(sOutRdPtr++); 
		if ( (int)(sOutRdPtr) >= (int)(sOutBuf+sOBUF_SIZE) ) sOutRdPtr = sOutBuf;
		U0THR = ch;
	} else   U0IER &= ~UIER_ETHREI;								// Disable THRE Int
	
	VICSoftIntClear = (1<<VIC_UART0);
	VICVectAddr = 0x00000000;             // clear this interrupt from the VIC
	
	ISR_EXIT();                           // recover registers and return
}

void ConsoleInit(int iDivider)  
{               
	PINSEL0 = (PINSEL0 & ~0x0000000F) | 0x00000005;	// Enable RxD0 and TxD0 
	U0LCR = 0x80|(1<<2)|0x3;        // 8 bits, no Parity, 2 Stop bit     
	U0DLL = iDivider & 0xFF;				// set divider / baud rate 
	U0DLM = iDivider >> 8;
	U0LCR = 0x03;  									// DLAB = 0                 
	
	U0FCR = 1;											// enable FIFO
	
	sOutWrPtr = sOutBuf;
	sOutRdPtr = sOutBuf;
	OutHCnt = 0;
	sOutFull = 0;	
	
	// disable UART0 interrupt
	VICIntEnClear |= 1<<VIC_UART0;	
		
  //  Setup the VIC for the UART
  VICIntSelect &= ~(1<<VIC_UART0);
  VICVectAddr5 = (unsigned int) Uart0ISR;
  VICVectCntl5 = VIC_ENABLE | VIC_UART0;
  
  VICIntEnable |= (1<<VIC_UART0);

  //  Enable UART0 interrupts
  U0IER |= UIER_ETHREI;								// Enable THRE Int
}

int putchar(int ch)  
{ 
	if ( sOutWrPtr==sOutRdPtr ) {		// buf empty
		if ( (U0LSR & 0x20) == 0 ) {
			*(sOutWrPtr++) = (unsigned char)ch;
			if ( (int)(sOutWrPtr) >= (int)(sOutBuf+sOBUF_SIZE) ) sOutWrPtr = sOutBuf;
		} else {
			U0THR = ch;
			OutHCnt++;
		}
		U0IER |= UIER_ETHREI;								// Enable THRE Int
		return ch;
	}
	
	*(sOutWrPtr++) = (unsigned char)ch;
	if ( (int)(sOutWrPtr) >= (int)(sOutBuf+sOBUF_SIZE) ) sOutWrPtr = sOutBuf;
	if ( sOutWrPtr != sOutRdPtr ) {
		return ch;
	}
	
	sOutFull = 1;	
	while ( sOutWrPtr == sOutRdPtr ) {
		U0IER |= UIER_ETHREI;								// Enable THRE Int

		delay(10);
	}
	sOutFull = 0;									
	return ch;
	
}

int getchar (void)  {                    /* Read character from Serial Port   */

  while (!(U0LSR & 0x01));

  return (U0RBR);
}

int my_putchar(int ch)  
{             
	if (U0LSR & 0x20) U0THR = ch;
	else ch = EOF;
	
	return ch;
}


int my_getchar (void)  {                 /* Read character from Serial Port   */

	if (U0LSR & 0x01) {
		return (U0RBR);
	} else {
		return (EOF);
	}
}


int puts(const char *s)
{
	while (*s) {
		putchar(*s++);
	}
	putchar('\n');
	return 1;
}


