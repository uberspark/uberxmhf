#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include "pal.h"
#include "trustvisor.h"

#define PAGE_SIZE ((uintptr_t) 4096)

static inline uint32_t vmcall(uint32_t eax, uint32_t ecx, uint32_t edx,
								uint32_t esi, uint32_t edi) {
	asm volatile ("vmcall\n\t" : "=a"(eax) : "a"(eax), "c"(ecx), "d"(edx),
					"S"(esi), "D"(edi));
	return eax;
}

uint32_t call_pal(uint32_t a, uint32_t b) {
	uint32_t b2 = b;
	// Call mmap(), construct struct tv_pal_sections
	int prot = PROT_EXEC | PROT_READ | PROT_WRITE;
	int mmap_flags = MAP_PRIVATE | MAP_ANONYMOUS;
	void *code = mmap(NULL, PAGE_SIZE, prot, mmap_flags, -1, 0);
	void *data = mmap(NULL, PAGE_SIZE, prot, mmap_flags, -1, 0);
	void *stack = mmap(NULL, PAGE_SIZE, prot, mmap_flags, -1, 0);
	void *param = mmap(NULL, PAGE_SIZE, prot, mmap_flags, -1, 0);
	struct tv_pal_sections *sections = malloc(sizeof(struct tv_pal_sections));
	assert(sections);
	sections->num_sections = 4;
	sections->sections[0] =
		(struct tv_pal_section) { TV_PAL_SECTION_CODE, (uintptr_t) code, 1 };
	sections->sections[1] =
		(struct tv_pal_section) { TV_PAL_SECTION_DATA, (uintptr_t) data, 1 };
	sections->sections[2] =
		(struct tv_pal_section) { TV_PAL_SECTION_STACK, (uintptr_t) stack, 1 };
	sections->sections[3] =
		(struct tv_pal_section) { TV_PAL_SECTION_PARAM, (uintptr_t) param, 1 };
	for (uint32_t i = 0; i < sections->num_sections; i++) {
		struct tv_pal_section *a = &(sections->sections[i]);
		assert(a->start_addr);
		memset((char *)(uintptr_t)(a->start_addr), 0x90, PAGE_SIZE * a->page_num);
		// If do not memset, XMHF will see a NULL page
		printf("Mmap: %u %p %u\n", a->type, a->start_addr, a->page_num);
	}
	printf("\n");
	fflush(stdout);
	// Construct struct tv_pal_params
	struct tv_pal_params *params = malloc(sizeof(struct tv_pal_params));
	assert(params);
	params->num_params = 2;
	params->params[0] = (struct tv_pal_param) { TV_PAL_PM_INTEGER, 4 };
	params->params[1] = (struct tv_pal_param) { TV_PAL_PM_POINTER, 4 };
	// Copy function .text
	uintptr_t begin_pal_off = (uintptr_t) begin_pal_c;
	uintptr_t end_pal_off = (uintptr_t) end_pal_c;
	uintptr_t my_pal_off = (uintptr_t) my_pal;
	memcpy(code, begin_pal_c, end_pal_off - begin_pal_off);
	uintptr_t reloc_my_pal_off = (uintptr_t)code + (my_pal_off - begin_pal_off);
	typeof(my_pal) *reloc_my_pal = (typeof(my_pal) *)reloc_my_pal_off;
	// Register scode
	assert(!vmcall(TV_HC_REG, (uint32_t)(uintptr_t)sections, 0,
					(uint32_t)(uintptr_t)params, (uint32_t)reloc_my_pal_off));
	// Call function
	printf("With PAL:\n");
	printf(" %u = *%p\n", b2, &b2);
	fflush(stdout);
	uint32_t ret = reloc_my_pal(a, &b2);
	printf(" %u = my_pal(%u, %p)\n", ret, a, &b2);
	printf(" %u = *%p\n\n", b2, &b2);
	fflush(stdout);
	// Unregister scode
	assert(!vmcall(TV_HC_UNREG, (uint32_t)reloc_my_pal_off, 0, 0, 0));
}

int main(int argc, char *argv[]) {
	uint32_t a, b, b2;
	uint32_t ret;
	assert(argc > 2);
	assert(sscanf(argv[1], "%u", &a) == 1);
	assert(sscanf(argv[2], "%u", &b) == 1);
	b2 = b;
	printf("Without PAL:\n");
	printf(" %u = *%p\n", b2, &b2);
	fflush(stdout);
	ret = my_pal(a, &b2);
	printf(" %u = my_pal(%u, %p)\n", ret, a, &b2);
	printf(" %u = *%p\n\n", b2, &b2);
	fflush(stdout);
	call_pal(a, b);
	return 0;
}

