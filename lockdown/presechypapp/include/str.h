/* string.h - string specific definitions
 * Written for SecVisor by Arvind Seshadri
 */
#ifndef __STRING_H__
#define __STRING_H__

#ifndef __ASSEMBLY__
extern void* init_memcpy(void*, void*, u32);
extern void* init_memset(void* , u32, u32);
extern u32 init_memcmp(void *s1, void *s2, u32 count);
extern void* memcpy(void*, void*, u32);
extern void* memset(void* , u32, u32);
extern u32 memcmp(void *s1, void *s2, u32 count);
extern size_t strlen(const char * s);
extern size_t strnlen(const char * s, u32);
extern char* strchr(const char *s, int c);
extern char* strncpy(char*, const char*, u32); 
extern u32 strncmp(u8 * cs, u8 * ct, u32 count);
#endif/* __ASSEMBLY__ */

#endif /* __STRING_H__ */
