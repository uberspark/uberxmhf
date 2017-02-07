/*
	debug module definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

void debug_hexdumpu32(u32 value){
    u32 num_bits;
    u8 ch;

    num_bits = 32;

    while(num_bits){
        num_bits -= 4;

        ch=(value >> num_bits) & 0xF;
        if(ch > 9)
        	ch += 0x37;
        else
        	ch += 0x30;

        bcm2837_miniuart_putc(ch);
    }

    bcm2837_miniuart_putc(' ');
    bcm2837_miniuart_putc('\n');
}
