#include <types.h>

inline char *strchr(const char *s, int c)
{
    long d0;
    register char *__res;
    __asm__ __volatile__ (
        "   mov  %%al,%%ah  \n"
        "1: lodsb           \n"
        "   cmp  %%ah,%%al  \n"
        "   je   2f         \n"
        "   test %%al,%%al  \n"
        "   jne  1b         \n"
        "   mov  $1,%1      \n"
        "2: mov  %1,%0      \n"
        "   dec  %0         \n"
        : "=a" (__res), "=&S" (d0) : "1" (s), "0" (c) );
    return __res;
}

/*
u32 strlen(const char * s)
{
	const char *sc;

	for (sc = s; *sc != '\0'; ++sc) ;
	return (u32)(sc - s);
}*/

u32 strnlen(const char * s, u32 count)
{
	const char *sc;

	for (sc = s; count-- && *sc != '\0'; ++sc);
	return (u32)(sc - s);
}


char* strncpy(char *dest, const char *src, u32 count)
{
	char *tmp = dest;
	
	count--;
	dest[count] = '\0';
	while (count-- && (*dest++ = *src++) != '\0');
	return tmp;
}

inline void *memcpy(void * to, const void * from, u32 n)
{
  int d0, d1, d2;

  __asm__ __volatile__(
  	"rep ; movsl\n\t"
  	"movl %4,%%ecx\n\t"
  	"andl $3,%%ecx\n\t"
#if 1	/* want to pay 2 byte penalty for a chance to skip microcoded rep? */
  	"jz 1f\n\t"
#endif
  	"rep ; movsb\n\t"
  	"1:"
  	: "=&c" (d0), "=&D" (d1), "=&S" (d2)
  	: "0" (n/4), "g" (n), "1" ((long) to), "2" ((long) from)
  	: "memory");
  return (to);
}

/*
 * memset(x,0,y) is a reasonably common thing to do, so we want to fill
 * things 32 bits at a time even when we don't know the size of the
 * area at compile-time..
 * attn: c must a 32 bit value, which means if you want to fill 0x90, you
 * must you 0x90909090 for c
 */
/*inline void *memset(void * s, u32 c, u32 count)
{
  int d0, d1;

  __asm__ __volatile__(
  	"rep ; stosl\n\t"
  	"testb $2,%b3\n\t"
  	"je 1f\n\t"
  	"stosw\n"
  	"1:\ttestb $1,%b3\n\t"
  	"je 2f\n\t"
  	"stosb\n"
  	"2:"
  	:"=&c" (d0), "=&D" (d1)
  	:"a" (c), "q" (count), "0" (count/4), "1" ((long) s)
  	:"memory");
  return (s);	
}*/

void *memset(void *str, u32 c, u32 len){
  register char *st = str;
  while (len-- > 0)
    *st++ = c;
  return str;
}


u32 strncmp(u8 * cs, u8 * ct, u32 count)
{
        int res;
        int d0, d1, d2;
        __asm__ __volatile__( "1:\tdecl %3\n\t"
                "js 2f\n\t"
                "lodsb\n\t"
                "scasb\n\t"
                "jne 3f\n\t" 
                "testb %%al,%%al\n\t"
                "jne 1b\n"
                "2:\txorl %%eax,%%eax\n\t"
                "jmp 4f\n"
                "3:\tsbbl %%eax,%%eax\n\t"
                "orb $1,%%al\n"
                "4:"
                :"=a" (res), "=&S" (d0), "=&D" (d1), "=&c" (d2)
                :"1" (cs),"2" (ct),"3" (count)
                :"memory");
        return (u32)res;
}





