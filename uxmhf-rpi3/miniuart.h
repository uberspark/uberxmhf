/*
	broadcom 2837 mini uart support

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __MINIUART_H__
#define __MINIUART_H__



#ifndef __ASSEMBLY__

void bcm2837_miniuart_init(void);
void bcm2837_miniuart_putc(u8 ch);
void bcm2837_miniuart_puts(char *buffer);
void bcm2837_miniuart_flush(void);


#endif // __ASSEMBLY__



#endif //__MINIUART_H__
