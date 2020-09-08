/*
	configuration

	author: amit vasudevan (amitvasudevan@acm.org)
*/


// configure script parameters

#define UXMHF_CORE_START_ADDR 	0x01000000
#define UXMHF_CORE_SIZE			0x02e00000

#define UXMHF_BOOT_PARTITION_START	8192
#define UXMHF_BOOT_PARTITION_END	137215


// computed parameters from above
#define UXMHF_CORE_END_ADDR 	( 0x01000000 + 0x02e00000 )


#ifndef __CONFIG_H__
#define __CONFIG_H__

#ifndef __ASSEMBLY__


#endif // __ASSEMBLY__


#endif //__CONFIG_H__
