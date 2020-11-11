/*
	configuration

	author: amit vasudevan (amitvasudevan@acm.org)
*/

// TBD: auto-generate these compile time definitions
#define __DEBUG_UART__ 1
#define __ENABLE_UART_MINI__ 1



// configure script parameters
//TBD: the start add is start of first public method sentinel section in uobjcoll.lscript
// end is the end of the last section in uobjcoll.lscript

#define UXMHF_CORE_START_ADDR 	0x01000000
#define UXMHF_CORE_SIZE			0x03000000

#define UXMHF_BOOT_PARTITION_START	8192
#define UXMHF_BOOT_PARTITION_END	137215


// computed parameters from above
#define UXMHF_CORE_END_ADDR 	( 0x01000000 + 0x02e00000 )


#ifndef __CONFIG_H__
#define __CONFIG_H__

#ifndef __ASSEMBLY__


#endif // __ASSEMBLY__


#endif //__CONFIG_H__
