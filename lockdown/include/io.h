/* io.h Functions to read and write I/O ports on x86
 * Modified from Xen for Visor by Elaine Shi and Arvind Seshadri
 */ 
#ifndef __IO_H_
#define __IO_H_

#ifndef __ASSEMBLY__

static inline void outl(u32 val, u32 port)
{
  /* N: constant in the range 0-255. used as a constraint for in and out 
   * a = eax, d = edx 
   */
  __asm__ __volatile__("out %0, %w1"
		     : /* no outputs */
		     :"a"(val), "Nd"((u16)port)); 
}

static inline void outw (u32 value, u32 port)
{
  __asm__ __volatile__ ("outw %w0,%w1": :"a" ((u16)value), "Nd" ((u16)port));
}

static inline void outb (u32 value, u32 port)
{                        
  __asm__ __volatile__ ("outb %b0,%w1": :"a" ((u8)value), "Nd" ((u16)port));
}

static inline u32 inl(u32 port)
{
  u32 val;
  
  __asm__ __volatile__("in %w1, %0"
		       :"=a"(val)
		       :"Nd"((u16)port));
  return val;
}

static inline unsigned short inw (u32 port)
{ 
  unsigned short _v;

  __asm__ __volatile__ ("inw %w1,%0":"=a" (_v):"Nd" ((u16)port));
  return _v;
}

static inline unsigned char inb (u32 port)
{ 
  unsigned char _v;
  
  __asm__ __volatile__ ("inb %w1,%0":"=a" (_v):"Nd" ((u16)port));
  return _v;
}

#endif /* __ASSEMBLY__ */

#endif /* __IO_H_ */
