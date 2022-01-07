#include <assert.h>
#include <stdio.h>

#include "pal.h"
#include "caller.h"
#include "trustvisor.h"

void call_pal(unsigned long a, unsigned long b) {
	unsigned long b2 = b;
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
	printf(" %lu = *%p\n", b2, &b2);
	fflush(stdout);
	unsigned long ret = func(a, &b2);
	printf(" %lu = my_pal(%lu, %p)\n", ret, a, &b2);
	printf(" %lu = *%p\n\n", b2, &b2);
	fflush(stdout);
	// Unregister scode
	unregister_pal(entry);
}

int main(int argc, char *argv[]) {
	unsigned long a, b, b2;
	unsigned long ret;
	assert(argc > 2);
	assert(sscanf(argv[1], "%lu", &a) == 1);
	assert(sscanf(argv[2], "%lu", &b) == 1);
	b2 = b;
	printf("Without PAL:\n");
	printf(" %lu = *%p\n", b2, &b2);
	fflush(stdout);
	ret = my_pal(a, &b2);
	printf(" %lu = my_pal(%lu, %p)\n", ret, a, &b2);
	printf(" %lu = *%p\n\n", b2, &b2);
	fflush(stdout);
	call_pal(a, b);
	return 0;
}

