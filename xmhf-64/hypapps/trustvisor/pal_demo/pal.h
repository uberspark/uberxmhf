#include <stdint.h>

extern void begin_pal_c();
extern uintptr_t my_pal(uintptr_t arg1, uintptr_t *arg2);
extern uintptr_t pal_10_int(uintptr_t arg0, uintptr_t arg1, uintptr_t arg2,
							uintptr_t arg3, uintptr_t arg4, uintptr_t arg5,
							uintptr_t arg6, uintptr_t arg7, uintptr_t arg8,
							uintptr_t arg9);
extern uintptr_t pal_10_ptr(uintptr_t *arg0, uintptr_t *arg1, uintptr_t *arg2,
							uintptr_t *arg3, uintptr_t *arg4, uintptr_t *arg5,
							uintptr_t *arg6, uintptr_t *arg7, uintptr_t *arg8,
							uintptr_t *arg9);
extern uintptr_t pal_5_ptr(uintptr_t size0, uintptr_t *ptr0, uintptr_t size1,
							uintptr_t *ptr1, uintptr_t size2, uintptr_t *ptr2,
							uintptr_t size3, uintptr_t *ptr3, uintptr_t size4,
							uintptr_t *ptr4);
extern void end_pal_c();
