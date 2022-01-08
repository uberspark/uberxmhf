#include "pal.h"

void begin_pal_c() {}

unsigned long my_pal(unsigned long arg1, unsigned long *arg2) {
	return arg1 + ((*arg2)++);
}

unsigned long pal_10_int(unsigned long arg0, unsigned long arg1,
						unsigned long arg2, unsigned long arg3,
						unsigned long arg4, unsigned long arg5,
						unsigned long arg6, unsigned long arg7,
						unsigned long arg8, unsigned long arg9) {
	unsigned long ans = 0;
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

unsigned long pal_10_ptr(unsigned long *arg0, unsigned long *arg1,
						unsigned long *arg2, unsigned long *arg3,
						unsigned long *arg4, unsigned long *arg5,
						unsigned long *arg6, unsigned long *arg7,
						unsigned long *arg8, unsigned long *arg9) {
	unsigned long ans = 0;
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

unsigned long pal_5_ptr(unsigned long size0, unsigned long *ptr0,
						unsigned long size1, unsigned long *ptr1,
						unsigned long size2, unsigned long *ptr2,
						unsigned long size3, unsigned long *ptr3,
						unsigned long size4, unsigned long *ptr4) {
	unsigned long ans = 0;
	unsigned long sizes[] = {size0, size1, size2, size3, size4};
	unsigned long *ptrs[] = {ptr0, ptr1, ptr2, ptr3, ptr4};
	unsigned long coeff = 1;
	for (int i = 0; i < 5; i++) {
		unsigned long size = sizes[i];
		unsigned long *ptr = ptrs[i];
		for (int j = 0; j < size; j++) {
			ans += ptr[j] * (coeff++);
			ptr[j] += (-1UL) / 0xffUL - 1UL;
		}
	}
	return ans;
}

void end_pal_c() {}
