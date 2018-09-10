# Micro-hypervisor based MAVLINK serial heart-beat (mavlinkserhb) uberapp

## Developer notes for mavlinkserhb

1. mavlinkserhb is controlled via the following components:
  1. a user-space application (`mavlinkserhb_userapp`) located at 
  `rgapps/linux/ugapp-mavlinkserhb/mavlinkserhb_userapp.c`
  1. a kernel-module (`mavlinkserhbkmod`) located at
  `rgapps/linux/ugapp-mavlinkserhb/mavlinkserhb_kmod.c`
  1. a hyptask uberapp (`uapp-mavlinkserhb`) located at
  `uapps/uapp-mavlinkserhb/uapp-mavlinkserhb.c`

1. `mavlinkserhb_userapp` interacts with `mavlinkserhbkmod` via a system-call, 
which in turn interacts with `uapp-mavlinkserhb` via a hypercall. 

1. the periodic heat-beat is designed to be handled by the function 
`uapp_mavlinkserhb_handleheartbeat` within `uapp-mavlinkserhb`. This periodic function
is created within the function `uapp_mavlinkserhb_handlehcall_initialize` within
`uapp-mavlinkserhb` with a period of 500ms (2Hz).  

1. the following are the serial hw functions available to implement the serial 
protocol within `uapp_mavlinkserhb_handleheartbeat` :
	1. `void uapp_mavlinkserhb_uart_init(void)` : this function initializes the 
	UART hardware
	1. `void uapp_mavlinkserhb_uart_flush(void)` : this function flushes the UART
	output (write) buffers
	1. `void uapp_mavlinkserhb_uart_send(u8 *buffer, u32 buf_len)` : this function
	sends (writes) a `buffer` of `buf_len` bytes to the UART. Note: You need to
	invoke `uapp_mavlinkserhb_uart_flush` explicitly after the send if you wish to
	flush the write buffer and ensure all bytes are written out prior to 
	performing any further operations.
	1. `int uapp_mavlinkserhb_uart_checkrecv(void)` : this function returns 1 if
	there are bytes waiting to be read from the UART receive buffer. A return
	value of 0 signifies an empty receive buffer.
	1. `int uapp_mavlinkserhb_uart_recv(u8 *buffer, u32 max_len, u32 *len_read)` :
	this function reads the UART receive buffer into the `buffer` specified 
	upto `max_len` bytes and returns the actual number of bytes read into 
	`len_read`. The function returns 1 if the UART receive buffer is empty 
	as a result	of this read. A return value of 0 indicates the UART receive
	buffer still has pending bytes to be read after this function returns 
	(e.g., if `max_len` was less than number of bytes in the UART receive
	buffer).
	 
	



## Instructions to build and deploy mavlinkserhb components

1.  Follow all instructions described in README.md and stop after 
building `uhcalltest` on development system

1. At this point build `mavlinkserhbkmod.ko` on development system
	1. `cd rgapps/linux/ugapp-mavlinkserhb`
	1. `make -C ~/linux ARCH=arm CROSS_COMPILE=~/tools/arm-bcm2708/gcc-linaro-arm-linux-gnueabihf-raspbian-x64/bin/arm-linux-gnueabihf- M=$PWD`
	1. `cp ./mavlinkserhbkmod.ko ~/uxmhf-rpi3-staging/.`

1. Build `mavlinkserhb_userapp` on development system
	1. `cd rgapps/linux`
	1. `make`
	1. `cd rgapps/linux/ugapp-mavlinkserhb`
	1. `make builduserapp`
	1. `cp ./mavlinkserhb_userapp ~/uxmhf-rpi3-staging/.`

1. Continue with remaining instructions described in README.md and boot the
micro-hypervisor with the uberguest



## Instructions to run mavlinkserhb

1. Install `mavlinkserhbkmod.ko` within uberguest once booted 
	1. `sudo insmod mavlinkserhbkmod.ko`

1. Run `mavlinkserhb_userapp` (mavlinkserhb user-mode test application) within uberguest to start heart-beat protocol
	1. `sudo ./mavlinkserhb_userapp`

1. Remove `mavlinkserhbkmod.ko` within uberguest once done
	1. `sudo rmmod uhcallkmod`

1. Shutdown the uberguest
	1. `sudo shutdown -hP now`

