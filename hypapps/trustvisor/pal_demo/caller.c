#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>

#include "vmcall.h"
#include "caller.h"

#define PAGE_SIZE ((uintptr_t) 4096)

static int lock_and_touch_page(void *addr, size_t len) {
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

/*
 * Auto-register a PAL
 * params: parameters description for TrustVisor
 * entry: entry function
 * begin_pal, end_pal: upper and lower bound of PAL
 * verbose: print mmap info
 * return: relocated entry point
 */
void *register_pal(struct tv_pal_params *params, void *entry, void *begin_pal,
					void *end_pal, int verbose) {
	// Call mmap(), construct struct tv_pal_sections
	int prot = PROT_EXEC | PROT_READ | PROT_WRITE;
	int mmap_flags = MAP_PRIVATE | MAP_ANONYMOUS;
	void *code = mmap(NULL, PAGE_SIZE, prot, mmap_flags, -1, 0);
	void *data = mmap(NULL, PAGE_SIZE, prot, mmap_flags, -1, 0);
	void *stack = mmap(NULL, PAGE_SIZE, prot, mmap_flags, -1, 0);
	void *param = mmap(NULL, PAGE_SIZE, prot, mmap_flags, -1, 0);
	struct tv_pal_sections sections = {
		num_sections: 4,
		sections: {
			{ TV_PAL_SECTION_CODE, 1, (uintptr_t) code },
			{ TV_PAL_SECTION_DATA, 1, (uintptr_t) data },
			{ TV_PAL_SECTION_STACK, 1, (uintptr_t) stack },
			{ TV_PAL_SECTION_PARAM, 1, (uintptr_t) param }
		}
	};
	for (uint32_t i = 0; i < sections.num_sections; i++) {
		struct tv_pal_section *a = &(sections.sections[i]);
		assert(a->start_addr);
		// Lock and touch page (prevent page getting swapping)
		void *start = (void *)(uintptr_t)(a->start_addr);
		size_t size = PAGE_SIZE * a->page_num;
		assert(!lock_and_touch_page(start, size));
		if (verbose) {
			printf("Mmap: %u %p %u\n", a->type, (void*)(uintptr_t)a->start_addr,
					a->page_num);
		}
	}
	if (verbose) {
		printf("\n");
		fflush(stdout);
	}
	// Copy function .text
	uintptr_t begin_pal_off = (uintptr_t)begin_pal;
	uintptr_t end_pal_off = (uintptr_t)end_pal;
	uintptr_t entry_off = (uintptr_t)entry;
	memcpy(code, begin_pal, end_pal_off - begin_pal_off);
	uintptr_t reloc_entry_off = (uintptr_t)code + (entry_off - begin_pal_off);
	void *reloc_entry = (void *)reloc_entry_off;
	// Register scode
	assert(!vmcall(TV_HC_REG, (uintptr_t)&sections, 0, (uintptr_t)params,
					reloc_entry_off));
	return reloc_entry;
}

/*
 * Auto-unregister a PAL
 * reloc_entry: relocated entry point (return value of register_pal())
 */
void unregister_pal(void *reloc_entry) {
	assert(!vmcall(TV_HC_UNREG, (uintptr_t)reloc_entry, 0, 0, 0));
}

