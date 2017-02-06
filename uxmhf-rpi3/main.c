#include <bcm2837.h>

typedef unsigned int u32;
typedef unsigned char u8;

extern u32 mmio_read32 (u32 address);
extern void mmio_write32 (u32 address, u32 value);
extern void delay_fn(void);

/* mini UART functions */
void bcm2837_miniuart_init(void){
    unsigned int gpio_fnsel, i;

    mmio_write32(AUX_ENABLES,1);
    mmio_write32(AUX_MU_IER_REG,0);
    mmio_write32(AUX_MU_CNTL_REG,0);
    mmio_write32(AUX_MU_LCR_REG,3);
    mmio_write32(AUX_MU_MCR_REG,0);
    mmio_write32(AUX_MU_IER_REG,0);
    mmio_write32(AUX_MU_IIR_REG,0xC6);
    mmio_write32(AUX_MU_BAUD_REG,270); //((250,000,000/115200)/8)-1 = 270

    gpio_fnsel=mmio_read32(GPFSEL1);
    gpio_fnsel &= ~(7<<12); //GPIO 14 (TX)
    gpio_fnsel |= 2<<12;    //GPIO 14 -- Alternate Function 5
    gpio_fnsel &= ~(7<<15); //GPIO 15 (RX)
    gpio_fnsel |= 2<<15;    //GPIO 15 -- Alternate Function 5
    mmio_write32(GPFSEL1,value);

    mmio_write32(GPPUD,0);
    for(i=0; i<150; i++) delay_fn();
    mmio_write32(GPPUDCLK0,(1<<14)|(1<<15));
    for(i=0; i<150; i++) delay_fn();
    mmio_write32(GPPUDCLK0,0);
    mmio_write32(AUX_MU_CNTL_REG,3);
}


void bcm2837_miniuart_putc(u8 ch){
    while(! (mmio_read32(AUX_MU_LSR_REG) & 0x20) );
    mmio_write32(AUX_MU_IO_REG,(u32)ch);
}

void bcm2837_miniuart_flush(void){
    while( (mmio_read32(AUX_MU_LSR_REG) & 0x100) );
}


void main(void){



}
