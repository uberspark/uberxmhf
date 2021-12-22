#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "pal.h"
#include "trustvisor.h"

#define PAGE_SIZE ((uintptr_t) 4096)

static inline uint32_t vmcall(uint32_t eax, uint32_t ecx, uint32_t edx,
								uint32_t esi, uint32_t edi) {
	asm volatile ("vmcall\n\t" : "=a"(eax) : "a"(eax), "c"(ecx), "d"(edx),
					"S"(esi), "D"(edi));
	return eax;
}

uint32_t call_pal(uint32_t a, uint32_t *b) {
	void *code = malloc(PAGE_SIZE);
	void *data = malloc(PAGE_SIZE);
	void *stack = malloc(PAGE_SIZE);
	void *param = malloc(PAGE_SIZE);
	assert(code);
	assert(data);
	assert(stack);
	assert(param);
	printf("%p\n", code);
	printf("%p\n", data);
	printf("%p\n", stack);
	printf("%p\n", param);
	struct tv_pal_sections *sections = malloc(sizeof(struct tv_pal_sections));
	struct tv_pal_params *params = malloc(sizeof(struct tv_pal_params));
	sections->num_sections = 4;
	sections->sections[0] =
		(struct tv_pal_section) { TV_PAL_SECTION_CODE, (uintptr_t) code, 1 };
	sections->sections[1] =
		(struct tv_pal_section) { TV_PAL_SECTION_DATA, (uintptr_t) data, 1 };
	sections->sections[2] =
		(struct tv_pal_section) { TV_PAL_SECTION_STACK, (uintptr_t) stack, 1 };
	sections->sections[3] =
		(struct tv_pal_section) { TV_PAL_SECTION_PARAM, (uintptr_t) param, 1 };
	params->num_params = 2;
	params->params[0] = (struct tv_pal_param) { TV_PAL_PM_INTEGER, 4 };
	params->params[0] = (struct tv_pal_param) { TV_PAL_PM_POINTER, 4 };
	// TODO: copy function .text
	// TODO: check return value
	vmcall(TV_HC_REG, (uint32_t) (uintptr_t) sections, 0,
			(uint32_t) (uintptr_t) params, (uint32_t) (uintptr_t) my_pal);
	// TODO: call function
}

int main(int argc, char *argv[]) {
	uint32_t a, b;
	uint32_t ret;
	assert(argc > 2);
	assert(sscanf(argv[1], "%u", &a) == 1);
	assert(sscanf(argv[2], "%u", &b) == 1);
	ret = my_pal(a, &b);
	printf("%u = my_pal(%u, &%u)\n", ret, a, b);
	call_pal(a, &b);
	return 0;
}

