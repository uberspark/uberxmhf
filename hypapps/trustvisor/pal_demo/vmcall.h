#include <stdint.h>

static inline uintptr_t vmcall(uintptr_t eax, uintptr_t ecx, uintptr_t edx,
								uintptr_t esi, uintptr_t edi) {
#ifdef VMCALL_OFFSET
	eax += VMCALL_OFFSET;
#endif
	asm volatile ("vmcall\n\t" : "+a"(eax) : "c"(ecx), "d"(edx), "S"(esi),
					"D"(edi));
	return eax;
}
