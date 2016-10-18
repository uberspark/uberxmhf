/*
 * XMHF rich guest app for aprvexec hypapp; low-level support functions
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

.section .text

// xhapprovexec test

.align 2097152
.global do_testxhapprovexec_functoprotect
do_testxhapprovexec_functoprotect:
	ret
.balign 2097152, 0x90

