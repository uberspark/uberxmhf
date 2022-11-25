#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "vmcall.h"
#include "pal.h"
#include "caller.h"
#include "trustvisor.h"

#define PASS_ARGS(args) args[0], args[1], args[2], args[3], args[4], \
						args[5], args[6], args[7], args[8], args[9]
#define PASS_ARGS_5(args1, args2)	args1[0], args2[0], args1[1], args2[1], \
									args1[2], args2[2], args1[3], args2[3], \
									args1[4], args2[4]

uintptr_t rand_long(void) {
	switch (0) { case 0:; case (RAND_MAX >= 0xff):; };
	uintptr_t ans = 0;
	for (int i = 0; i < sizeof(uintptr_t) * 8 / 8; i++) {
		ans <<= 8;
		ans |= ((uintptr_t)rand()) & 0xff;
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
		uintptr_t args[10];
		for (int i = 0; i < 10; i++) {
			args[i] = rand_long();
		}
		printf(".");
		fflush(stdout);
		args[0] &= ~PAL_FLAG_MASK;
		uintptr_t expected = pal_10_int(PASS_ARGS(args));
		args[0] |= PAL_FLAG_MASK;
		uintptr_t actual = func(PASS_ARGS(args));
		if (actual != expected) {
			result++;
			printf("Error: args = {%p, %p, %p, %p, %p, %p, %p, %p, %p, %p}, "
					"expected %p, actual %p\n", PASS_ARGS((void *)args),
					(void *)expected, (void *)actual);
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
		uintptr_t *args_expected[10];
		uintptr_t *args_actual[10];
		uintptr_t nums_original[21];
		uintptr_t nums_expected[21];
		uintptr_t nums_actual[21];
		for (int i = 0; i < 21; i++) {
			nums_original[i] = nums_expected[i] = nums_actual[i] = rand_long();
		}
		for (int i = 0; i < 10; i++) {
			args_expected[i] = &nums_expected[i * 2 + 1];
			args_actual[i] = &nums_actual[i * 2 + 1];
		}
		printf(".");
		fflush(stdout);
		args_expected[0][0] &= ~PAL_FLAG_MASK;
		uintptr_t expected = pal_10_ptr(PASS_ARGS(args_expected));
		args_actual[0][0] |= PAL_FLAG_MASK;
		uintptr_t actual = func(PASS_ARGS(args_actual));
		if (actual != expected) {
			result++;
			printf("Error: expected return %p, actual %p\n",
					(void *)expected, (void *)actual);
			fflush(stdout);
			continue;
		}
		for (int i = 0; i < 21; i++) {
			if (nums_expected[i] != nums_actual[i]) {
				result++;
				printf("Error: expected [%d] %p, actual %p, original %p\n", i,
						(void *)nums_expected[i], (void *)nums_actual[i],
						(void *)nums_original[i]);
				fflush(stdout);
				break;
			}
		}
	}
	// Unregister scode
	unregister_pal(entry);
	return result;
}

unsigned int test_5_ptr(unsigned int iters) {
	unsigned int result = 0;
	// Call function
	for (unsigned int iter = 0; iter < iters; iter++) {
		printf(".");
		fflush(stdout);
		// Generate pointer lengths
		uintptr_t args_i[5];
		size_t array_size = 1;
		for (int i = 0; i < 5; i++) {
			args_i[i] = rand_long() % 100;
			array_size += args_i[i] + 1;
		}
		// Allocate nums array
		uintptr_t *nums_original = malloc(array_size * sizeof(uintptr_t));
		uintptr_t *nums_expected = malloc(array_size * sizeof(uintptr_t));
		uintptr_t *nums_actual = malloc(array_size * sizeof(uintptr_t));
		for (int i = 0; i < array_size; i++) {
			nums_original[i] = nums_expected[i] = nums_actual[i] = rand_long();
		}
		// Set up pointers
		uintptr_t *args_p_expected[5];
		uintptr_t *args_p_actual[5];
		size_t cur_index = 1;
		for (int i = 0; i < 5; i++) {
			args_p_expected[i] = &nums_expected[cur_index];
			args_p_actual[i] = &nums_actual[cur_index];
			cur_index += args_i[i] + 1;
		}
		assert(cur_index == array_size);
		// Construct struct tv_pal_params
		struct tv_pal_params params = {
			num_params: 10,
			params: {
				{ TV_PAL_PM_INTEGER, 0 }, { TV_PAL_PM_POINTER, args_i[0] },
				{ TV_PAL_PM_INTEGER, 0 }, { TV_PAL_PM_POINTER, args_i[1] },
				{ TV_PAL_PM_INTEGER, 0 }, { TV_PAL_PM_POINTER, args_i[2] },
				{ TV_PAL_PM_INTEGER, 0 }, { TV_PAL_PM_POINTER, args_i[3] },
				{ TV_PAL_PM_INTEGER, 0 }, { TV_PAL_PM_POINTER, args_i[4] },
			}
		};
		// Dump info
		if (0) {
			printf("\narray_size = %p\n", (void *)array_size);
			for (int i = 0; i < 5; i++) {
				printf("args_i[%d] = %p\n", i, (void *)args_i[i]);
			}
			for (int i = 0; i < 5; i++) {
				printf("args_p_actual[%d] = %p\n", i, args_p_actual[i]);
			}
			for (int i = 0; i < 5; i++) {
				printf("args_p_expected[%d] = %p\n", i, args_p_expected[i]);
			}
			printf("nums_original = %p\n", nums_original);
			for (int i = 0; i < array_size; i++) {
				printf("nums_original[%d] = %p\n", i,
						(void *)nums_original[i]);
			}
			printf("nums_expected = %p\n", nums_expected);
			for (int i = 0; i < array_size; i++) {
				printf("pre  nums_expected[%d] = %p\n", i,
						(void *)nums_expected[i]);
			}
			printf("nums_actual = %p\n", nums_actual);
			for (int i = 0; i < array_size; i++) {
				printf("pre  nums_actual[%d] = %p\n", i,
						(void *)nums_actual[i]);
			}
		}
		// Update size0 with PAL flag
		assert((args_i[0] & PAL_FLAG_MASK) == 0);
		// Register scode
		void *entry = register_pal(&params, pal_5_ptr, begin_pal_c, end_pal_c,
									0);
		typeof(pal_5_ptr) *func = (typeof(pal_5_ptr) *)entry;
		args_i[0] &= ~PAL_FLAG_MASK;
		uintptr_t expected = pal_5_ptr(PASS_ARGS_5(args_i,
													args_p_expected));
		args_i[0] |= PAL_FLAG_MASK;
		uintptr_t actual = func(PASS_ARGS_5(args_i, args_p_actual));
		// Unregister scode
		unregister_pal(entry);
		// Dump info after calling
		if (0) {
			printf("nums_expected = %p\n", nums_expected);
			for (int i = 0; i < array_size; i++) {
				printf("post nums_expected[%d] = %p\n", i,
						(void *)nums_expected[i]);
			}
			printf("nums_actual = %p\n", nums_actual);
			for (int i = 0; i < array_size; i++) {
				printf("post nums_actual[%d] = %p\n", i,
						(void *)nums_actual[i]);
			}
		}
		// Check results
		if (actual != expected) {
			result++;
			printf("Error: expected return %p, actual %p\n",
					(void *)expected, (void *)actual);
			fflush(stdout);
			continue;
		}
		for (int i = 0; i < array_size; i++) {
			if (nums_expected[i] != nums_actual[i]) {
				result++;
				printf("Error: expected [%d] %p, actual %p, original %p\n", i,
						(void *)nums_expected[i], (void *)nums_actual[i],
						(void *)nums_original[i]);
				fflush(stdout);
				break;
			}
		}
		// Free
		free(nums_original);
		free(nums_expected);
		free(nums_actual);
	}
	return result;
}

int main(int argc, char *argv[]) {
	unsigned int funcs, iters, seed;
	if (!check_cpuid()) {
		printf("Error: TrustVisor not present according to CPUID\n");
		return 1;
	}
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
	if (funcs & 4) {
		result += test_5_ptr(iters);
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
