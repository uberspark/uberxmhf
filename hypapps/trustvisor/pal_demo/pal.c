#include "pal.h"

void begin_pal_c() {}

uintptr_t my_pal(uintptr_t arg1, uintptr_t *arg2) {
	return arg1 + ((*arg2)++);
}

uintptr_t pal_10_int(uintptr_t arg0, uintptr_t arg1, uintptr_t arg2,
						uintptr_t arg3, uintptr_t arg4, uintptr_t arg5,
						uintptr_t arg6, uintptr_t arg7, uintptr_t arg8,
						uintptr_t arg9) {
	uintptr_t ans = 0;
	ans += arg0 * 1;
	ans += arg1 * 2;
	ans += arg2 * 3;
	ans += arg3 * 4;
	ans += arg4 * 5;
	ans += arg5 * 6;
	ans += arg6 * 7;
	ans += arg7 * 8;
	ans += arg8 * 9;
	ans += arg9 * 10;
	return ans;
}

uintptr_t pal_10_ptr(uintptr_t *arg0, uintptr_t *arg1, uintptr_t *arg2,
						uintptr_t *arg3, uintptr_t *arg4, uintptr_t *arg5,
						uintptr_t *arg6, uintptr_t *arg7, uintptr_t *arg8,
						uintptr_t *arg9) {
	uintptr_t ans = 0;
	ans += ((*arg0)++) * 1;
	ans += ((*arg1)++) * 2;
	ans += ((*arg2)++) * 3;
	ans += ((*arg3)++) * 4;
	ans += ((*arg4)++) * 5;
	ans += ((*arg5)++) * 6;
	ans += ((*arg6)++) * 7;
	ans += ((*arg7)++) * 8;
	ans += ((*arg8)++) * 9;
	ans += ((*arg9)++) * 10;
	return ans;
}

uintptr_t pal_5_ptr(uintptr_t size0, uintptr_t *ptr0, uintptr_t size1,
					uintptr_t *ptr1, uintptr_t size2, uintptr_t *ptr2,
					uintptr_t size3, uintptr_t *ptr3, uintptr_t size4,
					uintptr_t *ptr4) {
	uintptr_t ans = 0;
	uintptr_t sizes[] = {size0, size1, size2, size3, size4};
	uintptr_t *ptrs[] = {ptr0, ptr1, ptr2, ptr3, ptr4};
	uintptr_t coeff = 1;
	for (int i = 0; i < 5; i++) {
		uintptr_t size = sizes[i];
		uintptr_t *ptr = ptrs[i];
		for (int j = 0; j < size; j++) {
			ans += ptr[j] * (coeff++);
			ptr[j] += (-1UL) / 0xffUL - 1UL;
		}
	}
	return ans;
}

void end_pal_c() {}
