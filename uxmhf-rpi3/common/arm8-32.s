/*
	ARM 8 32-bit low-level cpu state access functions

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>

.section ".text"

.globl mmio_write32
mmio_write32:
    str r1,[r0]
    bx lr

.globl mmio_read32
mmio_read32:
    ldr r0,[r0]
    bx lr

.globl sysreg_read_spsr_hyp
sysreg_read_spsr_hyp:
	mrs r0, SPSR_hyp
	bx lr


.globl sysreg_read_scr
sysreg_read_scr:
	mrc p15, 0, r0, c1, c1, 0
	bx lr

.globl sysreg_read_cpsr
sysreg_read_cpsr:
	mrs r0, cpsr
	bx lr

.global sysreg_read_hvbar
sysreg_read_hvbar:
	mrc p15, 4, r0, c12, c0, 0
	bx lr


.global sysreg_write_hvbar
sysreg_write_hvbar:
	mcr p15, 4, r0, c12, c0, 0
	bx lr


.global sysreg_read_hcr
sysreg_read_hcr:
	mrc p15, 4, r0, c1, c1, 0
	bx lr

.global sysreg_write_hcr
sysreg_write_hcr:
	mcr p15, 4, r0, c1, c1, 0
	bx lr

.global sysreg_read_hsctlr
sysreg_read_hsctlr:
	mrc p15, 4, r0, c1, c0, 0
	bx lr

.global sysreg_write_hsctlr
sysreg_write_hsctlr:
	mcr p15, 4, r0, c1, c0, 0
	bx lr

.global hypcall
hypcall:
	hvc #0
	bx lr

.global svccall
svccall:
	svc #0
	bx lr

.global sysreg_read_sctlr
sysreg_read_sctlr:
	mrc p15, 0, r0, c1, c0, 0
	bx lr

.global sysreg_write_sctlr
sysreg_write_sctlr:
	mcr p15, 0, r0, c1, c0, 0
	bx lr

.global sysreg_read_vbar
sysreg_read_vbar:
	mrc p15, 0, r0, c12, c0, 0
	bx lr

.global sysreg_write_vbar
sysreg_write_vbar:
	mcr p15, 0, r0, c12, c0, 0
	bx lr

.global sysreg_read_vtcr
sysreg_read_vtcr:
	mrc p15, 4, r0, c2, c1, 2
	bx lr

.global sysreg_write_vtcr
sysreg_write_vtcr:
	mcr p15, 4, r0, c2, c1, 2
	bx lr

.global sysreg_read_hdcr
sysreg_read_hdcr:
	mrc p15, 4, r0, c1, c1, 1
	bx lr

.global sysreg_write_hdcr
sysreg_write_hdcr:
	mcr p15, 4, r0, c1, c1, 1
	bx lr

.global sysreg_read_hcptr
sysreg_read_hcptr:
	mrc p15, 4, r0, c1, c1, 2
	bx lr

.global sysreg_write_hcptr
sysreg_write_hcptr:
	mcr p15, 4, r0, c1, c1, 2
	bx lr

.global sysreg_read_hstr
sysreg_read_hstr:
	mrc p15, 4, r0, c1, c1, 3
	bx lr

.global sysreg_write_hstr
sysreg_write_hstr:
	mcr p15, 4, r0, c1, c1, 3
	bx lr

//returns a 64-bit value:
//r0=lower 32-bits; r1=upper 32-bits (c.f. AAPCS)
.global sysreg_read_vttbr
sysreg_read_vttbr:
	mrrc p15, 6, r0, r1, c2
	bx lr

//inputs: 64-bit value
//r0=lower 32-bits; r1=upper 32-bits (c.f. AAPCS)
.global sysreg_write_vttbr
sysreg_write_vttbr:
	mcrr p15, 6, r0, r1, c2
	bx lr


.global sysreg_read_hsr
sysreg_read_hsr:
	mrc p15, 4, r0, c5, c2, 0
	bx lr
