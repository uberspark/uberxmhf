.section .text
.align 0x4
.global mmio_write32
mmio_write32: 
dsb st
str r1, [r0, 0]
bx lr
.section .text
.align 0x4
.global mmio_read32
mmio_read32: 
ldr r0, [r0, 0]
bx lr
.section .text
.align 0x4
.global sysreg_read_spsr_hyp
sysreg_read_spsr_hyp: 
mrs r0, SPSR_hyp
bx lr
.section .text
.align 0x4
.global sysreg_read_scr
sysreg_read_scr: 
mrc p15, 0, r0, c1, c1, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_cpsr
sysreg_read_cpsr: 
mrs r0, cpsr
bx lr
.section .text
.align 0x4
.global sysreg_write_cpsr
sysreg_write_cpsr: 
msr cpsr, r0
bx lr
.section .text
.align 0x4
.global sysreg_read_hvbar
sysreg_read_hvbar: 
mrc p15, 4, r0, c12, c0, 0
bx lr
.section .text
.align 0x4
.global sysreg_write_hvbar
sysreg_write_hvbar: 
mcr p15, 4, r0, c12, c0, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_hcr
sysreg_read_hcr: 
mrc p15, 4, r0, c1, c1, 0
bx lr
.section .text
.align 0x4
.global sysreg_write_hcr
sysreg_write_hcr: 
mcr p15, 4, r0, c1, c1, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_hsctlr
sysreg_read_hsctlr: 
mrc p15, 4, r0, c1, c0, 0
bx lr
.section .text
.align 0x4
.global sysreg_write_hsctlr
sysreg_write_hsctlr: 
isb
mcr p15, 4, r0, c1, c0, 0
isb
bx lr
.section .text
.align 0x4
.global sysreg_read_actlr
sysreg_read_actlr: 
mrc p15, 0, r0, c1, c0, 1
bx lr
.section .text
.align 0x4
.global sysreg_write_actlr
sysreg_write_actlr: 
mcr p15, 0, r0, c1, c0, 1
bx lr
.section .text
.align 0x4
.global sysreg_read_idisar4
sysreg_read_idisar4: 
mrc p15, 0, r0, c0, c2, 4
bx lr
.section .text
.align 0x4
.global cpu_isb
cpu_isb: 
isb
bx lr
.section .text
.align 0x4
.global cpu_dsb
cpu_dsb: 
dsb
bx lr
.section .text
.align 0x4
.global cpu_dmbish
cpu_dmbish: 
dmb ish
bx lr
.section .text
.align 0x4
.global cpu_read_sp
cpu_read_sp: 
mov r0, sp
bx lr
.section .text
.align 0x4
.global hypcall
hypcall: 
hvc #0
bx lr
.section .text
.align 0x4
.global svccall
svccall: 
svc #0
bx lr
.section .text
.align 0x4
.global sysreg_read_sctlr
sysreg_read_sctlr: 
mrc p15, 0, r0, c1, c0, 0
bx lr
.section .text
.align 0x4
.global sysreg_write_sctlr
sysreg_write_sctlr: 
mcr p15, 0, r0, c1, c0, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_vbar
sysreg_read_vbar: 
mrc p15, 0, r0, c12, c0, 0
bx lr
.section .text
.align 0x4
.global sysreg_write_vbar
sysreg_write_vbar: 
mcr p15, 0, r0, c12, c0, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_vtcr
sysreg_read_vtcr: 
mrc p15, 4, r0, c2, c1, 2
bx lr
.section .text
.align 0x4
.global sysreg_write_vtcr
sysreg_write_vtcr: 
mcr p15, 4, r0, c2, c1, 2
bx lr
.section .text
.align 0x4
.global sysreg_read_hdcr
sysreg_read_hdcr: 
mrc p15, 4, r0, c1, c1, 1
bx lr
.section .text
.align 0x4
.global sysreg_write_hdcr
sysreg_write_hdcr: 
mcr p15, 4, r0, c1, c1, 1
bx lr
.section .text
.align 0x4
.global sysreg_read_hcptr
sysreg_read_hcptr: 
mrc p15, 4, r0, c1, c1, 2
bx lr
.section .text
.align 0x4
.global sysreg_write_hcptr
sysreg_write_hcptr: 
mcr p15, 4, r0, c1, c1, 2
bx lr
.section .text
.align 0x4
.global sysreg_read_hstr
sysreg_read_hstr: 
mrc p15, 4, r0, c1, c1, 3
bx lr
.section .text
.align 0x4
.global sysreg_write_hstr
sysreg_write_hstr: 
mcr p15, 4, r0, c1, c1, 3
bx lr
.section .text
.align 0x4
.global sysreg_read_vttbr
sysreg_read_vttbr: 
mrrc p15,6,r0,r1,c2
bx lr
.section .text
.align 0x4
.global sysreg_write_vttbr
sysreg_write_vttbr: 
mcrr p15, 6, r0, r1, c2
bx lr
.section .text
.align 0x4
.global sysreg_read_hsr
sysreg_read_hsr: 
mrc p15, 4, r0, c5, c2, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_elrhyp
sysreg_read_elrhyp: 
mrs r0, ELR_hyp
bx lr
.section .text
.align 0x4
.global sysreg_write_elrhyp
sysreg_write_elrhyp: 
msr ELR_hyp, r0
bx lr
.section .text
.align 0x4
.global sysreg_tlbiallh
sysreg_tlbiallh: 
mcr p15, 4, r0, c8, c7, 0
dsb ish
bx lr
.section .text
.align 0x4
.global sysreg_iciallu
sysreg_iciallu: 
mcr p15, 0, r0, c7, c5, 0
bx lr
.section .text
.align 0x4
.global sysreg_tlbiipas2is
sysreg_tlbiipas2is: 
mcr p15, 4, r0, c8, c0, 1
isb
dsb ish
bx lr
.section .text
.align 0x4
.global sysreg_tlbiallis
sysreg_tlbiallis: 
mcr p15, 0, r0, c8, c3, 0
isb
dsb ish
bx lr
.section .text
.align 0x4
.global sysreg_read_mair0
sysreg_read_mair0: 
mrc p15, 0, r0, c10, c2, 0
bx lr
.section .text
.align 0x4
.global sysreg_write_mair0
sysreg_write_mair0: 
mcr p15, 0, r0, c10, c2, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_mair1
sysreg_read_mair1: 
mrc p15, 0, r0, c10, c2, 1
bx lr
.section .text
.align 0x4
.global sysreg_write_mair1
sysreg_write_mair1: 
mcr p15, 0, r0, c10, c2, 1
bx lr
.section .text
.align 0x4
.global sysreg_read_hmair0
sysreg_read_hmair0: 
mrc p15, 4, r0, c10, c2, 0
bx lr
.section .text
.align 0x4
.global sysreg_write_hmair0
sysreg_write_hmair0: 
mcr p15, 4, r0, c10, c2, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_hmair1
sysreg_read_hmair1: 
mrc p15, 4, r0, c10, c2, 1
bx lr
.section .text
.align 0x4
.global sysreg_write_hmair1
sysreg_write_hmair1: 
mcr p15, 4, r0, c10, c2, 1
bx lr
.section .text
.align 0x4
.global sysreg_read_httbr
sysreg_read_httbr: 
mrrc p15,4,r0,r1,c2
bx lr
.section .text
.align 0x4
.global sysreg_write_httbr
sysreg_write_httbr: 
mcrr p15, 4, r0, r1, c2
bx lr
.section .text
.align 0x4
.global sysreg_read_htcr
sysreg_read_htcr: 
mrc p15, 4, r0, c2, c0, 2
bx lr
.section .text
.align 0x4
.global sysreg_write_htcr
sysreg_write_htcr: 
mcr p15, 4, r0, c2, c0, 2
bx lr
.section .text
.align 0x4
.global sysreg_read_dacr
sysreg_read_dacr: 
mrc p15, 0, r0, c3, c0, 0
bx lr
.section .text
.align 0x4
.global sysreg_write_dacr
sysreg_write_dacr: 
mcr p15, 0, r0, c3, c0, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_hdfar
sysreg_read_hdfar: 
mrc p15, 4, r0, c6, c0, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_hpfar
sysreg_read_hpfar: 
mrc p15, 4, r0, c6, c0, 4
bx lr
.section .text
.align 0x4
.global spin_lock
spin_lock: 
mov r1, 0
one: 
ldrex r2, [r0, 0]
teq r2, 1
wfene
strexeq r3, r1, [r0, 0]
teqeq r3, 0
bne one
dmb ish
bx lr
.section .text
.align 0x4
.global spin_unlock
spin_unlock: 
dmb ish
mov r1, 1
str r1, [r0, 0]
dsb ishst
sev
bx lr
.section .text
.align 0x4
.global sysreg_read_ttbcr
sysreg_read_ttbcr: 
mrc p15, 0, r0, c2, c0, 2
bx lr
.section .text
.align 0x4
.global sysreg_write_ttbcr
sysreg_write_ttbcr: 
mcr p15, 0, r0, c2, c0, 2
bx lr
.section .text
.align 0x4
.global sysreg_read_ttbr0
sysreg_read_ttbr0: 
mrc p15, 0, r0, c2, c0, 0
bx lr
.section .text
.align 0x4
.global sysreg_write_ttbr0
sysreg_write_ttbr0: 
mcr p15, 0, r0, c2, c0, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_ttbr1
sysreg_read_ttbr1: 
mrc p15, 0, r0, c2, c0, 1
bx lr
.section .text
.align 0x4
.global sysreg_write_ttbr1
sysreg_write_ttbr1: 
mcr p15, 0, r0, c2, c0, 1
bx lr
.section .text
.align 0x4
.global sysreg_ats12nsour
sysreg_ats12nsour: 
mcr p15, 0, r0, c7, c8, 6
bx lr
.section .text
.align 0x4
.global sysreg_ats1cpr
sysreg_ats1cpr: 
mcr p15, 0, r0, c7, c8, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_par
sysreg_read_par: 
mrc p15, 0, r0, c7, c4, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_cntpct
sysreg_read_cntpct: 
mrrc p15,0,r0,r1,c14
bx lr
.section .text
.align 0x4
.global sysreg_read_cnthp_tval
sysreg_read_cnthp_tval: 
mrc p15, 4, r0, c14, c2, 0
bx lr
.section .text
.align 0x4
.global sysreg_write_cnthp_tval
sysreg_write_cnthp_tval: 
mcr p15, 4, r0, c14, c2, 0
bx lr
.section .text
.align 0x4
.global sysreg_read_cnthp_ctl
sysreg_read_cnthp_ctl: 
mrc p15, 4, r0, c14, c2, 1
bx lr
.section .text
.align 0x4
.global sysreg_write_cnthp_ctl
sysreg_write_cnthp_ctl: 
mcr p15, 4, r0, c14, c2, 1
bx lr
