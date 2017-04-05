/*
	debug module definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

extern __attribute__(( section(".data") )) u32 xdprintfsmp_lock=1;


// gcc requires this for division by 0 on 64-bit values; used for debugging output
void raise(void){
	bcm2837_miniuart_puts("uXMHF-rpi3: core: compiler raise invoked -- division by 0!\n");
	bcm2837_miniuart_puts("uXMHF-rpi3: core: Halting!\n");
	HALT();
}


void debug_hexdumpu32(u32 value){
    u32 num_bits;
    u32 ch;

    num_bits = 32;

    while(num_bits){
        num_bits -= 4;

        ch=(value >> num_bits) & 0xF;
        if(ch > 9)
        	ch += 0x37;
        else
        	ch += 0x30;

        bcm2837_miniuart_putc((u8)ch);
    }

    bcm2837_miniuart_putc(' ');
    bcm2837_miniuart_putc('\n');
}
