/*
	configuration

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __CONFIG_H__
#define __CONFIG_H__


// TBD: auto-generate these compile time definitions via uobjcoll manifest
#define UXMHF_CORE_START_ADDR 	0x01000000
#define UXMHF_CORE_SIZE			0x03000000
#define UXMHF_CORE_END_ADDR 	( 0x01000000 + 0x02e00000 )
#define UXMHF_BOOT_PARTITION_START	8192
#define UXMHF_BOOT_PARTITION_END	137215


//#define __SECBOOT__
//#define __DMAPROT__
//#define __INTPROT__
//#define __FIQREFLECTION__
#define __DEBUG_UART__
#define __ENABLE_UART_MINI__
//#define __ENABLE_UART_PL011__
//#define __ENABLE_UART_PL011_CTSRTS__

//#define __ENABLE_UAPP_CTXTRACE__
//#define __ENABLE_UAPP_PA5ENCFS__
//#define __ENABLE_UAPP_PVDRIVER_UART__
//#define __ENABLE_UAPP_UAGENT__
//#define __ENABLE_UAPP_UHCALLTEST__
//#define __ENABLE_UAPP_UHSIGN__
//#define __ENABLE_UAPP_UHSTATEDB__
//#define __ENABLE_UAPP_UTPMTEST__
//#define __ENABLE_UAPP_WATCHDOG__





#ifndef __ASSEMBLY__


#endif // __ASSEMBLY__


#endif //__CONFIG_H__
