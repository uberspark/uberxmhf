/* print.h header file for printf and friends 
 * Modified from Xen for SecVisor by Arvind Seshadri
 */

#ifndef __PRINT_H_
#define __PRINT_H_

#define print_string putstr

#ifndef __ASSEMBLY__

void init_uart(void);
void putstr(const char *str);

#if defined(__DEBUG_SERIAL__) || defined(__DEBUG_VGA__)
extern void printf(const char *format, ...)
  __attribute__ ((format (printf, 1, 2)));
#else
#define printf(format, args...) ((void)0)
#endif

#endif /* __ASSEMBLY__ */

#endif /* __PRINT_H_ */
