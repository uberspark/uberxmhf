#include <assert.h>
#include <stdio.h>
#include <string.h>

#ifdef WINDOWS
#include <memoryapi.h>
#include <errhandlingapi.h>
#else /* !WINDOWS */
#include <sys/mman.h>
#endif /* WINDOWS */

#include "vmcall.h"
#include "caller.h"

#define PAGE_SIZE ((uintptr_t) 4096)

#define MAX_PAL_RECORDS 10

/* Record PALs in user level */
typedef struct pal_record_t {
	/* Where the user should call, NULL if invalid record */
	void *user_entry;
	/* Boundary between untrusted app and PAL */
	uintptr_t pal_entry;
	void *mmap_code;
	void *mmap_data;
	void *mmap_stack;
	void *mmap_param;
#ifdef TRANSLATE
	void *mmap_code2;
#endif /* TRANSLATE */
} pal_record_t;

static pal_record_t pal_records[MAX_PAL_RECORDS];

static pal_record_t *get_pal_record(void *user_entry) {
	for (int i = 0; i < MAX_PAL_RECORDS; i++) {
		if (pal_records[i].user_entry == user_entry) {
			return &pal_records[i];
		}
	}
	while (1) {
		assert(0 && "PAL record not found");
	}
}


#ifdef TRANSLATE
extern void *windows2linux();
extern void *windows2linux_call();
extern void *windows2linux_call_end();
extern void *windows2linux_end();
extern void *linux2windows();
extern void *linux2windows_call();
extern void *linux2windows_call_end();
extern void *linux2windows_end();

/*
 * Relocate a function (callee) that calls another function (callee). The
 * caller's template is defined by plt*. The caller should be relocated to
 * address starting at target. After relocating, the caller should call callee.
 *
 * Between plt_call and plt_call_end, there should be a movabs function.
 * For example:
 *  48 b8 10 32 54 76 98    movabs $0xfedcba9876543210,%rax
 *  ba dc fe 
 *
 * plt: start of template function
 * plt_call: before call instruction
 * plt_call_end: after call instruction
 * plt_end: end of template function
 * plt_magic: magic number in template call instruction
 * target: target memory to relocate function to
 * callee: function to call after relocation
 * return: relocated function entry point
 */
static void *relocate_func(void *plt, void *plt_call, void *plt_call_end,
							void *plt_end, uintptr_t plt_magic, void *target,
							void *callee) {
	assert(plt < plt_call);
	assert(plt_call + 10 == plt_call_end);
	assert(plt_call_end < plt_end);
	memcpy(target, plt, plt_end - plt);
	uintptr_t *callee_addr = target + (plt_call - plt) + 2;
	assert(*callee_addr == plt_magic);
	*callee_addr = (uintptr_t)callee;
	return target;
}
#endif /* TRANSLATE */

static int lock_and_touch_page(void *addr, size_t len) {
#ifdef WINDOWS
	if (!VirtualLock(addr, len)) {
		DWORD err = GetLastError();
		printf("VirtualLock error: %lx\n", err);
		return 1;
	}
#else /* !WINDOWS */
	// Call mlock() and then write to page
	// similar to tv_lock_range() and tv_touch_range() in tee-sdk
	if (mlock(addr, len)) {
		perror("mlock");
		return 1;
	}
#endif /* WINDOWS */
	// If do not memset, XMHF will see a NULL page
	memset(addr, 0x90, len);
	return 0;
}

/* Call VirtualAlloc on Windows and mmap on Linux */
static void *mmap_wrap(size_t length) {
#ifdef WINDOWS
	DWORD prot = PAGE_EXECUTE_READWRITE;
	DWORD va_flags = MEM_COMMIT | MEM_RESERVE;
	return VirtualAlloc(NULL, PAGE_SIZE, va_flags, prot);
#else /* !WINDOWS */
	int prot = PROT_EXEC | PROT_READ | PROT_WRITE;
	int mmap_flags = MAP_PRIVATE | MAP_ANONYMOUS;
	return mmap(NULL, PAGE_SIZE, prot, mmap_flags, -1, 0);
#endif /* WINDOWS */
}

/* Call VirtualFree on Windows and munmap on Linux */
static int munmap_wrap(void *addr) {
#ifdef WINDOWS
	return !(VirtualFree(addr, 0, MEM_RELEASE));
#else /* !WINDOWS */
	return munmap(addr, PAGE_SIZE);
#endif /* WINDOWS */
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
	void *code = mmap_wrap(PAGE_SIZE);
	void *data = mmap_wrap(PAGE_SIZE);
	void *stack = mmap_wrap(PAGE_SIZE);
	void *param = mmap_wrap(PAGE_SIZE);
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
	// Copy function .text
	uintptr_t begin_pal_off = (uintptr_t)begin_pal;
	uintptr_t end_pal_off = (uintptr_t)end_pal;
	uintptr_t entry_off = (uintptr_t)entry;
	memcpy(code, begin_pal, end_pal_off - begin_pal_off);
	/* Boundary between untrusted app and PAL */
	uintptr_t pal_entry = (uintptr_t)code + (entry_off - begin_pal_off);
	/* Where the user should call */
	void *user_entry = (void *)pal_entry;
#ifdef TRANSLATE
	void *code2 = mmap_wrap(PAGE_SIZE);
	{
		// Relocate linux2windows
		void *target = code + end_pal_off - begin_pal_off;
		user_entry = relocate_func(
			linux2windows, linux2windows_call, linux2windows_call_end,
			linux2windows_end, 0xfedcba9876543210UL, target, user_entry);
		// PAL boundary between windows2linux() and linux2windows_call()
		pal_entry = (uintptr_t)user_entry;
		// Relocate windows2linux
		target = code2;
		assert(target);
		if (verbose) {
			printf("Mmap:   %p\n", target);
		}
		user_entry = relocate_func(
			windows2linux, windows2linux_call, windows2linux_call_end,
			windows2linux_end, 0x0123456789abcdefUL, target, user_entry);
		// Currently the wrapper has to read 10 arguments, so if params is not
		// large enough there will be pagefault on accessing stack.
		while (params->num_params < TV_MAX_PARAMS) {
			params->params[params->num_params].type = TV_PAL_PM_INTEGER;
			params->params[params->num_params].size = 0;
			params->num_params++;
		}
	}
#endif /* TRANSLATE */
	if (verbose) {
		printf("\n");
		fflush(stdout);
	}
	// Register PAL locally
	pal_record_t *pal_record = get_pal_record(NULL);
	pal_record->user_entry = user_entry;
	pal_record->pal_entry = pal_entry;
	pal_record->mmap_code = code;
	pal_record->mmap_data = data;
	pal_record->mmap_stack = stack;
	pal_record->mmap_param = param;
#ifdef TRANSLATE
	pal_record->mmap_code2 = code2;
#endif /* TRANSLATE */
	// Register scode
	assert(!vmcall(TV_HC_REG, (uintptr_t)&sections, 0, (uintptr_t)params,
					pal_entry));
	return user_entry;
}

/*
 * Auto-unregister a PAL
 * user_entry: relocated entry point (return value of register_pal())
 */
void unregister_pal(void *user_entry) {
	pal_record_t *pal_record = get_pal_record(user_entry);
	assert(!vmcall(TV_HC_UNREG, pal_record->pal_entry, 0, 0, 0));
	assert(!munmap_wrap(pal_record->mmap_code));
	assert(!munmap_wrap(pal_record->mmap_data));
	assert(!munmap_wrap(pal_record->mmap_stack));
	assert(!munmap_wrap(pal_record->mmap_param));
#ifdef TRANSLATE
	assert(!munmap_wrap(pal_record->mmap_code2));
#endif /* TRANSLATE */
}

