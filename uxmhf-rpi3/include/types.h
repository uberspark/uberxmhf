/*
	base types

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __TYPES_H__
#define __TYPES_H__

#include <config.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdarg.h>
#include <string.h>


#ifndef __ASSEMBLY__

typedef unsigned int u32;
typedef unsigned char u8;
typedef unsigned long long u64;

#endif // __ASSEMBLY__


#define UXMHF_CORE_START_ADDR (0x28000000)
#define UXMHF_CORE_END_ADDR (0x28000000+0xC00000)



#endif //__TYPES_H__
