#include <stdint.h>

static inline uint32_t vmcall(uint32_t eax, uint32_t ecx, uint32_t edx,
								uint32_t esi, uint32_t edi) {
	asm volatile ("vmcall\n\t" : "=a"(eax) : "a"(eax), "c"(ecx), "d"(edx),
					"S"(esi), "D"(edi));
	return eax;
}

