/*
	MAVLINK serial heart-beat uberapp

	author: amit vasudevan (amitvasudevan@acm.org)
*/

//////////////////////////////////////////////////////////////////////////////
// headers
//////////////////////////////////////////////////////////////////////////////

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

#include <hypmtscheduler.h>
#include <mavlinkserhb.h>


//////////////////////////////////////////////////////////////////////////////
// mavlinkserhb serial port hw interface
//////////////////////////////////////////////////////////////////////////////


//////
// initialize UART hardware for 115200 8N1
//////
void uapp_mavlinkserhb_uart_init(void){
    unsigned int gpio_fnsel, i;

    mmio_write32(AUX_ENABLES,1);
    mmio_write32(AUX_MU_IER_REG,0);		//clear interrupt enable
    mmio_write32(AUX_MU_CNTL_REG,0);
    mmio_write32(AUX_MU_LCR_REG,3);
    mmio_write32(AUX_MU_MCR_REG,0);
    mmio_write32(AUX_MU_IER_REG,0);
    mmio_write32(AUX_MU_IIR_REG,0xC6);
    mmio_write32(AUX_MU_BAUD_REG,270); //((250,000,000/115200)/8)-1 = 270

    gpio_fnsel=mmio_read32(GPFSEL1);
    gpio_fnsel &= ~(7<<12); 			//GPIO 14 (TX)
    gpio_fnsel |= 2<<12;    			//GPIO 14 -- Alternate Function 5
    gpio_fnsel &= ~(7<<15); 			//GPIO 15 (RX)
    gpio_fnsel |= 2<<15;    			//GPIO 15 -- Alternate Function 5
    mmio_write32(GPFSEL1,gpio_fnsel);

    mmio_write32(GPPUD,0);
    for(i=0; i<150; i++);				//delay
    mmio_write32(GPPUDCLK0,(1<<14)|(1<<15));
    for(i=0; i<150; i++);				//delay
    mmio_write32(GPPUDCLK0,0);
    mmio_write32(AUX_MU_CNTL_REG,3);
}



//////
// flush FIFO queue
//////
void uapp_mavlinkserhb_uart_flush(void){
    while( (mmio_read32(AUX_MU_LSR_REG) & 0x100) );
}


//////
// check is we have something in receive queue
// return 1 if true, else 0
//////
int uapp_mavlinkserhb_uart_checkrecv(void){

	if( mmio_read32(AUX_MU_LSR_REG) & 0x01 ) return 1;
    return 0;
}


//////
// write bytes to UART
//////
void uapp_mavlinkserhb_uart_send(u8 *buffer, u32 buf_len){
	u32 i;

	for(i=0; i < buf_len; i++){
	    while(! (mmio_read32(AUX_MU_LSR_REG) & 0x20) );
	    mmio_write32(AUX_MU_IO_REG,(u32)buffer[i]);
	}
}


//////
// read bytes from UART until max_len or read buffer exhausted
// return 0: read buffer still has characters
// return 1: read buffer exhausted
//////
int uapp_mavlinkserhb_uart_recv(u8 *buffer, u32 max_len, u32 *len_read){
	u32 i;

	i=0;
	while(uapp_mavlinkserhb_uart_checkrecv()){
		buffer[i] = mmio_read32(AUX_MU_IO_REG) & 0xFF;
		i++;
		if(i == max_len)
			break;
	}

	*len_read = i;

	if(uapp_mavlinkserhb_uart_checkrecv())
		return 0;
	else
		return 1;
}


//////////////////////////////////////////////////////////////////////////////





//////////////////////////////////////////////////////////////////////////////
// mavlinkserhb async timer functions
//////////////////////////////////////////////////////////////////////////////


//////
// the periodic function which handles the heart-beat protocol
//////
void uapp_mavlinkserhb_handleheartbeat(struct sched_timer *t){
	bcm2837_miniuart_puts("mavlinkserhb: periodic heart-beat handler fired\n");
}

//////////////////////////////////////////////////////////////////////////////





//////////////////////////////////////////////////////////////////////////////
// mavlinkserhb hypercall APIs
//////////////////////////////////////////////////////////////////////////////

//////
// mavlinkserhb initialize hypercall API
// creates the heart-beat thread to begin processing mavlink heart-beat
// messages
//////
uapp_mavlinkserhb_handlehcall_initialize(uapp_mavlinkserhb_param_t *mlhbsp){

	//declare a timer to deal with heart-beat
	uapp_sched_timer_declare((0.5 * HYPMTSCHEDULER_TIME_1SEC),
			(0.5 * HYPMTSCHEDULER_TIME_1SEC), 99, &uapp_mavlinkserhb_handleheartbeat);

	//bcm2837_miniuart_puts("mavlinkserhb: initialize hypercall\n");
}



//////
// top-level hypercall handler hub
// return true if handled the hypercall, false if not
//////
bool uapp_mavlinkserhb_handlehcall(u32 uhcall_function, void *uhcall_buffer,
		u32 uhcall_buffer_len){
	uapp_mavlinkserhb_param_t *mlhbsp;

	if(uhcall_function != UAPP_MAVLINKSERHB_UHCALL){
		return false;
	}

	mlhbsp = (uapp_mavlinkserhb_param_t *)uhcall_buffer;

	if(mlhbsp->uhcall_fn == UAPP_MAVLINKSERHB_UHCALL_INITIALIZE){
		uapp_mavlinkserhb_handlehcall_initialize(mlhbsp);

	}else{
		//ignore unknown uhcall_fn silently

	}

	return true;
}


//////////////////////////////////////////////////////////////////////////////




//////////////////////////////////////////////////////////////////////////////
// mavlinkserhb initialization
//////////////////////////////////////////////////////////////////////////////

//////
// the main initialization function
//////
void uapp_mavlinkserhb_initialize(u32 cpuid){

	if(cpuid == 0){
		_XDPRINTFSMP_("%s[%u]: Initializing mavlinkserhb...\n", __func__, cpuid);

	}else{
		_XDPRINTFSMP_("%s[%u]: AP CPU: nothing to do, moving on...\n", __func__, cpuid);
	}


}


//////////////////////////////////////////////////////////////////////////////
