#include <assert.h>
#include <stdio.h>

#include "vmcall.h"
#include "pal.h"
#include "caller.h"
#include "trustvisor.h"

void call_pal(uintptr_t a, uintptr_t b) {
	uintptr_t b2 = b;
	// Construct struct tv_pal_params
	struct tv_pal_params params = {
		num_params: 2,
		params: {
			{ TV_PAL_PM_INTEGER, 4 },
			{ TV_PAL_PM_POINTER, 4 }
		}
	};
	// Register scode
	void *entry = register_pal(&params, my_pal, begin_pal_c, end_pal_c, 1);
	typeof(my_pal) *func = (typeof(my_pal) *)entry;
	// Call function
	printf("With PAL:\n");
	printf(" %p = *%p\n", (void *)b2, &b2);
	fflush(stdout);
	uintptr_t ret = func(a | PAL_FLAG_MASK, &b2);
	printf(" %p = my_pal(%p, %p)\n", (void *)ret, (void *)a, &b2);
	printf(" %p = *%p\n\n", (void *)b2, &b2);
	fflush(stdout);
	// Unregister scode
	unregister_pal(entry);
}

int main(int argc, char *argv[]) {
	uintptr_t a, b, b2;
	uintptr_t ret;
	if (!check_cpuid()) {
		printf("Error: TrustVisor not present according to CPUID\n");
		return 1;
	}
	assert(argc > 2);
	assert(sscanf(argv[1], "%p", (void **)&a) == 1);
	assert(sscanf(argv[2], "%p", (void **)&b) == 1);
	b2 = b;
	printf("Without PAL:\n");
	printf(" %p = *%p\n", (void *)b2, &b2);
	a &= ~PAL_FLAG_MASK;
	fflush(stdout);
	ret = my_pal(a, &b2);
	printf(" %p = my_pal(%p, %p)\n", (void *)ret, (void *)a, &b2);
	printf(" %p = *%p\n\n", (void *)b2, &b2);
	fflush(stdout);
	call_pal(a, b);
	return 0;
}
