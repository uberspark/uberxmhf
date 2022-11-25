#include "pal.h"
#include "vmcall.h"

void begin_pal_c() {}

/*
 * The 31th bit of arg indicates whether PAL is expected.
 * When return this bit is set to 0.
 */
uintptr_t pal_check_cpuid(uintptr_t *arg) {
	uint32_t eax, ebx, ecx, edx;
	int expected = (*arg) & PAL_FLAG_MASK;
	*arg &= ~PAL_FLAG_MASK;
	cpuid(&eax, &ebx, &ecx, &edx);
	if (eax != 0x7a767274U) {
		return 1;
	}
	if (expected) {
		if (ebx == 0xffffffffU) {
			return 2;
		}
	} else {
		if (ebx != 0xffffffffU) {
			return 3;
		}
	}
	return 0;
}

uintptr_t my_pal(uintptr_t arg1, uintptr_t *arg2) {
	{
		uintptr_t checked = pal_check_cpuid(&arg1);
		if (checked) {
			return 0xdead0000U + checked;
		}
	}
	return arg1 + ((*arg2)++);
}

uintptr_t pal_10_int(uintptr_t arg0, uintptr_t arg1, uintptr_t arg2,
						uintptr_t arg3, uintptr_t arg4, uintptr_t arg5,
						uintptr_t arg6, uintptr_t arg7, uintptr_t arg8,
						uintptr_t arg9) {
	{
		uintptr_t checked = pal_check_cpuid(&arg0);
		if (checked) {
			return 0xdead0000U + checked;
		}
	}
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
	{
		uintptr_t checked = pal_check_cpuid(arg0);
		if (checked) {
			return 0xdead0000U + checked;
		}
	}
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
	{
		uintptr_t checked = pal_check_cpuid(&size0);
		if (checked) {
			return 0xdead0000U + checked;
		}
	}
	uintptr_t ans = 0;
	uintptr_t sizes[] = {size0, size1, size2, size3, size4};
	uintptr_t *ptrs[] = {ptr0, ptr1, ptr2, ptr3, ptr4};
	uintptr_t coeff = 1;
	for (int i = 0; i < 5; i++) {
		uintptr_t size = sizes[i];
		uintptr_t *ptr = ptrs[i];
		for (int j = 0; j < size; j++) {
			ans += ptr[j] * (coeff++);
			ptr[j] += (uintptr_t)0x3141592653589793ULL;
		}
	}
	return ans;
}

void end_pal_c() {}
