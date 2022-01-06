#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include "pal.h"
#include "vmcall.h"
#include "trustvisor.h"

#define PAGE_SIZE ((uintptr_t) 4096)

int lock_and_touch_page(void *addr, size_t len) {
	// Call mlock() and then write to page
	// similar to tv_lock_range() and tv_touch_range() in tee-sdk
	if (mlock(addr, len)) {
		perror("mlock");
		return 1;
	}
	// If do not memset, XMHF will see a NULL page
	memset(addr, 0x90, len);
	return 0;
}

void call_pal(unsigned long a, unsigned long b) {
	unsigned long b2 = b;
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
		(struct tv_pal_section) { TV_PAL_SECTION_CODE, 1, (uintptr_t) code };
	sections->sections[1] =
		(struct tv_pal_section) { TV_PAL_SECTION_DATA, 1, (uintptr_t) data };
	sections->sections[2] =
		(struct tv_pal_section) { TV_PAL_SECTION_STACK, 1, (uintptr_t) stack };
	sections->sections[3] =
		(struct tv_pal_section) { TV_PAL_SECTION_PARAM, 1, (uintptr_t) param };
	for (uint32_t i = 0; i < sections->num_sections; i++) {
		struct tv_pal_section *a = &(sections->sections[i]);
		assert(a->start_addr);
		// Lock and touch page (prevent page getting swapping)
		void *start = (void *)(uintptr_t)(a->start_addr);
		size_t size = PAGE_SIZE * a->page_num;
		assert(!lock_and_touch_page(start, size));
		printf("Mmap: %u %p %u\n", a->type, (void*)(uintptr_t)a->start_addr,
				a->page_num);
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
	assert(!vmcall(TV_HC_REG, (uintptr_t)sections, 0, (uintptr_t)params,
					reloc_my_pal_off));
	// Call function
	printf("With PAL:\n");
	printf(" %lu = *%p\n", b2, &b2);
	fflush(stdout);
	unsigned long ret = reloc_my_pal(a, &b2);
	printf(" %lu = my_pal(%lu, %p)\n", ret, a, &b2);
	printf(" %lu = *%p\n\n", b2, &b2);
	fflush(stdout);
	// Unregister scode
	assert(!vmcall(TV_HC_UNREG, (uintptr_t)reloc_my_pal_off, 0, 0, 0));
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

