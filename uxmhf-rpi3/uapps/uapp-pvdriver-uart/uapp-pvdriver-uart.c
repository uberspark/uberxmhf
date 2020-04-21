#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <uart.h>
#include <debug.h>

#include <uapp-pvdriver-uart.h>

//////////////////////////////////////////////////////////////////////////////
// UART para-virtualized driver interfaces
//////////////////////////////////////////////////////////////////////////////


//////
// initialize UART hardware for 115200 baudrate
// 8 stop bits, no parity, 1 stop bit configuration (8N1)
//////
void uapp_pvdriver_uart_init(void){
    uart_init();
}

//////
// write bytes to UART
//////
void uapp_pvdriver_uart_send(u8 *buffer, u32 buf_len){
	u32 i;

	for(i=0; i < buf_len; i++){
        uart_putc(buffer[i]);
	}
}

//////
// read bytes from UART until max_len or read buffer exhausted
// return 0: read buffer still has characters
// return 1: read buffer exhausted
//////
int uapp_pvdriver_uart_recv(u8 *buffer, u32 max_len, u32 *len_read){
	u32 i;

	i=0;
	while(uart_can_recv()){
		uart_getc(&buffer[i]);
		i++;
		if(i == max_len)
			break;
	}

	*len_read = i;

	if(uart_can_recv())
		return 0;
	else
		return 1;
}


//////
// check if we can send via UART
// return 0: if we __cannot__ send
// return 1: if we __can__ send
//////
int uapp_pvdriver_uart_can_send(void){
    if(uart_can_send())
        return 1;
    else
        return 0;
}

//////
// check if we have something to receive from UART
// return 0: if we __dont have__ anything to read
// return 1: if we __have__ something to read
//////
int uapp_pvdriver_uart_can_recv(void){
    if(uart_can_recv())
        return 1;
    else
        return 0;
}


//////
// flush FIFO
//////
void uapp_pvdriver_uart_flush(void){
    uart_flush();
}




//////////////////////////////////////////////////////////////////////////////
