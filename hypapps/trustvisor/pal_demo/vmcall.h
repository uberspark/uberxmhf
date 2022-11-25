#include <stdint.h>

__attribute__((always_inline))
inline void cpuid(uint32_t *eax, uint32_t *ebx, uint32_t *ecx, uint32_t *edx)
{
	uint32_t a = 0x7a567254U, c = 0U;
#ifdef VMCALL_OFFSET
	c += VMCALL_OFFSET;
#endif
	asm volatile("cpuid" : "=a"(*(eax)), "=b"(*(ebx)), "=c"(*(ecx)),
					"=d"(*(edx)) : "0"(a), "2"(c));
}

static inline uintptr_t vmcall(uintptr_t eax, uintptr_t ecx, uintptr_t edx,
								uintptr_t esi, uintptr_t edi) {
#ifdef VMCALL_OFFSET
	eax += VMCALL_OFFSET;
#endif
	asm volatile ("vmcall\n\t" : "+a"(eax) : "c"(ecx), "d"(edx), "S"(esi),
					"D"(edi));
	return eax;
}
