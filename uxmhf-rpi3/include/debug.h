/*
	debug module definitions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __DEBUG_H__
#define __DEBUG_H__

#ifndef __ASSEMBLY__


void debug_hexdumpu32(u32 value);

#define HALT() while(1);

#endif // __ASSEMBLY__



#endif //__DEBUG_H__
