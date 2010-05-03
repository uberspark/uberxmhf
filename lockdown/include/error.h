//error.h - error handling within the hypervisor
//author: amit vasudevan (amitvasudevan@acm.org)
#ifndef __ERROR_H_
#define __ERROR_H_

#ifndef __ASSEMBLY__

#define HALT()	__asm__ __volatile__ ("hlt\r\n");

#define HALTV86M()	__asm__ __volatile__ (".byte 0xEB, 0xFE\r\n");

#define RESET()	__asm__ __volatile__ ("ud2\r\n");


#define ASSERT(_p) { if ( !(_p) ) { printf("\nAssertion '%s' failed, line %d, file %s\n", #_p , __LINE__, __FILE__); HALT(); } }

#define WARNING(_p) { if ( !(_p) ) { printf("Warning Assertion '%s' failed, line %d, file %s\n", #_p , __LINE__, __FILE__);} }


#endif /*__ASSEMBLY__*/


#endif /* _ERROR_H */
