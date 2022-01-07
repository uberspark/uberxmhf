#include <stdint.h>

extern void begin_pal_c();
extern unsigned long my_pal(unsigned long arg1, unsigned long *arg2);
extern unsigned long pal_10_int(unsigned long arg0, unsigned long arg1,
								unsigned long arg2, unsigned long arg3,
								unsigned long arg4, unsigned long arg5,
								unsigned long arg6, unsigned long arg7,
								unsigned long arg8, unsigned long arg9);
extern unsigned long pal_10_ptr(unsigned long *arg0, unsigned long *arg1,
								unsigned long *arg2, unsigned long *arg3,
								unsigned long *arg4, unsigned long *arg5,
								unsigned long *arg6, unsigned long *arg7,
								unsigned long *arg8, unsigned long *arg9);
extern unsigned long pal_5_ptr(unsigned long size0, unsigned long *ptr0,
								unsigned long size1, unsigned long *ptr1,
								unsigned long size2, unsigned long *ptr2,
								unsigned long size3, unsigned long *ptr3,
								unsigned long size4, unsigned long *ptr4);
extern void end_pal_c();
