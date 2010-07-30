/* types.h - define sdata types for 32-bit x86
 * Modified from Xen for SecVisor by Elaine Shi and Arvind Seshadri
 */

#ifndef __TYPES_H_
#define __TYPES_H_

#define BITS_PER_LONG 32

#ifndef __ASSEMBLY__

#define INT_MAX         ((int)(~0U>>1))
#define INT_MIN         (-INT_MAX - 1)
#define UINT_MAX        (~0U)
#define LONG_MAX        ((long)(~0UL>>1))
#define LONG_MIN        (-LONG_MAX - 1)
#define ULONG_MAX       (~0UL)


#ifndef NULL
#define NULL ((void*)0)
#endif


#define FILE			void

typedef unsigned char u8;
typedef signed char s8;
typedef unsigned short u16;
typedef signed short s16;
typedef unsigned int u32;
typedef signed int s32;
typedef unsigned long long u64;
typedef signed long long s64;
typedef unsigned int size_t;

typedef s32 int32_t;
typedef u32 uint32_t;
typedef u32 u_int32_t;
typedef u16 uint16_t;
typedef u16 u_int16_t;
typedef u8  uint8_t;
typedef u8  u_int8_t;
typedef u64 uint64_t;

typedef u32 paddr_t;
typedef void * dma_addr_t;

#endif /*ifndef __ASSEMBLY__*/

#endif /* __TYPES_H_ */
