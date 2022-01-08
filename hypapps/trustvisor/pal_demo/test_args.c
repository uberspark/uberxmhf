#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "pal.h"
#include "caller.h"
#include "trustvisor.h"

#define PASS_ARGS(args) args[0], args[1], args[2], args[3], args[4], \
						args[5], args[6], args[7], args[8], args[9]

unsigned long rand_long(void) {
	switch (0) { case 0:; case (RAND_MAX >= 0xffff):; };
	unsigned long ans = 0;
	for (int i = 0; i < sizeof(long) * 8 / 16; i++) {
		ans <<= 16;
		ans |= ((unsigned long)rand()) & 0xffff;
	}
	return ans;
}

unsigned int test_10_int(unsigned int iters) {
	unsigned int result = 0;
	// Construct struct tv_pal_params
	struct tv_pal_params params = {
		num_params: 10,
		params: {
			{ TV_PAL_PM_INTEGER, 0 }, { TV_PAL_PM_INTEGER, 0 },
			{ TV_PAL_PM_INTEGER, 0 }, { TV_PAL_PM_INTEGER, 0 },
			{ TV_PAL_PM_INTEGER, 0 }, { TV_PAL_PM_INTEGER, 0 },
			{ TV_PAL_PM_INTEGER, 0 }, { TV_PAL_PM_INTEGER, 0 },
			{ TV_PAL_PM_INTEGER, 0 }, { TV_PAL_PM_INTEGER, 0 },
		}
	};
	// Register scode
	void *entry = register_pal(&params, pal_10_int, begin_pal_c, end_pal_c, 0);
	typeof(pal_10_int) *func = (typeof(pal_10_int) *)entry;
	// Call function
	for (unsigned int iter = 0; iter < iters; iter++) {
		unsigned long args[10];
		for (int i = 0; i < 10; i++) {
			args[i] = rand_long();
		}
		printf(".");
		fflush(stdout);
		unsigned long expected = pal_10_int(PASS_ARGS(args));
		unsigned long actual = func(PASS_ARGS(args));
		if (actual != expected) {
			result++;
			printf("Error: args = {%lu, %lu, %lu, %lu, %lu, %lu, %lu, %lu, "
					"%lu, %lu}, expected %lu, actual %lu\n", PASS_ARGS(args),
					expected, actual);
			fflush(stdout);
		}
	}
	// Unregister scode
	unregister_pal(entry);
	return result;
}

unsigned int test_10_ptr(unsigned int iters) {
	unsigned int result = 0;
	// Construct struct tv_pal_params
	struct tv_pal_params params = {
		num_params: 10,
		params: {
			{ TV_PAL_PM_POINTER, 1 }, { TV_PAL_PM_POINTER, 1 },
			{ TV_PAL_PM_POINTER, 1 }, { TV_PAL_PM_POINTER, 1 },
			{ TV_PAL_PM_POINTER, 1 }, { TV_PAL_PM_POINTER, 1 },
			{ TV_PAL_PM_POINTER, 1 }, { TV_PAL_PM_POINTER, 1 },
			{ TV_PAL_PM_POINTER, 1 }, { TV_PAL_PM_POINTER, 1 },
		}
	};
	// Register scode
	void *entry = register_pal(&params, pal_10_ptr, begin_pal_c, end_pal_c, 0);
	typeof(pal_10_ptr) *func = (typeof(pal_10_ptr) *)entry;
	// Call function
	for (unsigned int iter = 0; iter < iters; iter++) {
		unsigned long *args_expected[10];
		unsigned long *args_actual[10];
		unsigned long nums_original[21];
		unsigned long nums_expected[21];
		unsigned long nums_actual[21];
		for (int i = 0; i < 21; i++) {
			nums_original[i] = nums_expected[i] = nums_actual[i] = rand_long();
		}
		for (int i = 0; i < 10; i++) {
			args_expected[i] = &nums_expected[i * 2 + 1];
			args_actual[i] = &nums_actual[i * 2 + 1];
		}
		printf(".");
		fflush(stdout);
		unsigned long expected = pal_10_ptr(PASS_ARGS(args_expected));
		unsigned long actual = func(PASS_ARGS(args_actual));
		if (actual != expected) {
			result++;
			printf("Error: expected return %lu, actual %lu\n",
					expected, actual);
			fflush(stdout);
			continue;
		}
		for (int i = 0; i < 21; i++) {
			if (nums_expected[i] != nums_actual[i]) {
				result++;
				printf("Error: expected [i] %lu, actual %lu, original %lu\n",
						nums_expected[i], nums_actual[i], nums_original[i]);
				fflush(stdout);
				break;
			}
		}
	}
	// Unregister scode
	unregister_pal(entry);
	return result;
}

int main(int argc, char *argv[]) {
	unsigned int funcs, iters, seed;
	assert(argc > 3);
	assert(sscanf(argv[1], "%u", &funcs) == 1);
	assert(sscanf(argv[2], "%u", &iters) == 1);
	assert(sscanf(argv[3], "%u", &seed) == 1);
	srand(seed);
	unsigned result = 0;
	if (funcs & 1) {
		result += test_10_int(iters);
	}
	if (funcs & 2) {
		result += test_10_ptr(iters);
	}
	if (result) {
		printf("\nTest failed\n");
		fflush(stdout);
		return 1;
	} else {
		printf("\nTest pass\n");
		fflush(stdout);
		return 0;
	}
}

