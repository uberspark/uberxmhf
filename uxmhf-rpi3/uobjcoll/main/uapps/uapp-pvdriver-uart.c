/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */


#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/debug.h>

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/uapp-pvdriver-uart.h>

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
	while(uart_getc(&buffer[i])){
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


//////////////////////////////////////////////////////////////////////////////
// pvdriver_uart hypercall APIs
//////////////////////////////////////////////////////////////////////////////

////// init
void uapp_pvdriver_uart_handlehcall_init(uapp_pvdriver_uart_param_t *hparams){

	//init
	uapp_pvdriver_uart_init();

	hparams->status=1;
}


////// send
void uapp_pvdriver_uart_handlehcall_send(uapp_pvdriver_uart_param_t *hparams){
	//iparam_1 = buffer physical address
	//iparam_2 = buffer length (in bytes)

	//sanity check buffer length, currently only a max of 4096 bytes
	//can be sent at a time
	if(hparams->iparam_2 > 4096){
		hparams->status=0;
		return;
	}

	//send the bytes out through the UART and flush output
	uapp_pvdriver_uart_send(hparams->iparam_1, hparams->iparam_2);
	uapp_pvdriver_uart_flush();

	//set status to indicate success
	hparams->status=1;
}




////// recv
void uapp_pvdriver_uart_handlehcall_recv(uapp_pvdriver_uart_param_t *hparams){
	//iparam_1 = buffer physical address
	//iparam_2 = buffer max length (in bytes)

	//oparam_1 = length read
	//oparam_2 = UART read buffer status (1=exhausted, 0=not exhausted)

	//sanity check buffer length, currently only a max of 4096 bytes
	//can be received at a time
	if(hparams->iparam_2 > 4096){
		hparams->status=0;
		return;
	}

	//read bytes from UART
	hparams->oparam_2 = uapp_pvdriver_uart_recv(hparams->iparam_1, hparams->iparam_2, &hparams->oparam_1);

	//set status to indicate success
	hparams->status=1;
}



////// can_send
void uapp_pvdriver_uart_handlehcall_can_send(uapp_pvdriver_uart_param_t *hparams){

	if(uapp_pvdriver_uart_can_send())
		hparams->status=1;
	else
		hparams->status=0;

	return;
}

////// can_recv
void uapp_pvdriver_uart_handlehcall_can_recv(uapp_pvdriver_uart_param_t *hparams){

	if(uapp_pvdriver_uart_can_recv())
		hparams->status=1;
	else
		hparams->status=0;

	return;
}

////// flush
void uapp_pvdriver_uart_handlehcall_flush(uapp_pvdriver_uart_param_t *hparams){
    uapp_pvdriver_uart_flush();
    hparams->status=1;
}


////// hypercall handler hub
////// return true if handled the hypercall, false if not
bool uapp_pvdriver_uart_handlehcall(u32 uhcall_function, void *uhcall_buffer,
		u32 uhcall_buffer_len){
	uapp_pvdriver_uart_param_t *hparams;

	if(uhcall_function != UAPP_PVDRIVER_UART_UHCALL){
		return false;
	}

	hparams = (uapp_pvdriver_uart_param_t *)uhcall_buffer;

	if(hparams->uhcall_fn == UAPP_PVDRIVER_UART_UHCALL_INIT){
		uapp_pvdriver_uart_handlehcall_init(hparams);

	}else if(hparams->uhcall_fn == UAPP_PVDRIVER_UART_UHCALL_SEND){
			uapp_pvdriver_uart_handlehcall_send(hparams);

	}else if(hparams->uhcall_fn == UAPP_PVDRIVER_UART_UHCALL_RECV){
			uapp_pvdriver_uart_handlehcall_recv(hparams);

	}else if(hparams->uhcall_fn == UAPP_PVDRIVER_UART_UHCALL_CAN_SEND){
			uapp_pvdriver_uart_handlehcall_can_send(hparams);

	}else if(hparams->uhcall_fn == UAPP_PVDRIVER_UART_UHCALL_CAN_RECV){
			uapp_pvdriver_uart_handlehcall_can_recv(hparams);

	}else if(hparams->uhcall_fn == UAPP_PVDRIVER_UART_UHCALL_FLUSH){
			uapp_pvdriver_uart_handlehcall_flush(hparams);

	}else{
		//ignore unknown uhcall_fn silently

	}

	return true;
}


//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
// main uapp initialization
//////////////////////////////////////////////////////////////////////////////

void uapp_pvdriver_uart_initialize_uapp(u32 cpuid){

    //only initialize for boot-cpu
	if(cpuid == 0){
		_XDPRINTFSMP_("%s[%u]: Initializing UART para-virtualized driver backend...\n", __func__, cpuid);
	}
    
}


//////////////////////////////////////////////////////////////////////////////
