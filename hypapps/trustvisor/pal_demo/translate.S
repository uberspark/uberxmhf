/*
 * Translate between Windows calling convention and Linux for x86_64
 *
 * Registers:
 *
 * | Register name | Windows | Linux   |
 * |---------------|---------|---------|
 * | RAX           | return  | return  |
 * | RBX           | callee  | callee  |
 * | RCX           | arg1    | arg4    |
 * | RDX           | arg2    | arg3    |
 * | RSI           | callee  | arg2    |
 * | RDI           | callee  | arg1    |
 * | RBP           | callee  | callee  |
 * | RSP           | callee  | callee  |
 * | R8            | arg3    | arg5    |
 * | R9            | arg4    | arg6    |
 * | R10           | caller  | caller  |
 * | R11           | caller  | caller  |
 * | R12           | callee  | callee  |
 * | R13           | callee  | callee  |
 * | R14           | callee  | callee  |
 * | R15           | callee  | callee  |
 *
 * Stack:
 * * Windows: arg1 - arg10
 * * Linux: arg7 - arg10
 */

/*
 * A Windows function calls this function, this function calls a Linux function
 *
 * The stack looks like
 * | Addr | Addr | Content | Pointer |
 * |------|------|---------|---------|
 * | 96   | 128  | arg10   |         |
 * | 88   | 120  | arg9    |         |
 * | 80   | 112  | arg8    |         |
 * | 72   | 104  | arg7    |         |
 * | 64   | 96   | arg6    |         |
 * | 56   | 88   | arg5    |         |
 * | 48   | 80   | (arg4)  |         |
 * | 40   | 72   | (arg3)  |         |
 * | 32   | 64   | (arg2)  |         |
 * | 24   | 56   | (arg1)  |         |
 * | 16   | 48   | return  | old rsp |
 * | 8    | 40   | rsi     |         |
 * | 0    | 32   | rdi     |         |
 * |      | 24   | arg10   |         |
 * |      | 16   | arg9    |         |
 * |      | 8    | arg8    |         |
 * |      | 0    | arg7    |         |
 */
.global windows2linux
.global windows2linux_call
.global windows2linux_call_end
.global windows2linux_end

windows2linux:
	pushq	%rsi
	pushq	%rdi
	pushq	96(%rsp)
	pushq	96(%rsp)
	pushq	96(%rsp)
	pushq	96(%rsp)
	movq	%rcx, %rdi
	movq	%rdx, %rsi
	movq	%r8, %rdx
	movq	%r9, %rcx
	movq	96(%rsp), %r9
	movq	88(%rsp), %r8
windows2linux_call:
	movq	$0x0123456789abcdef, %rax
windows2linux_call_end:
	call	*%rax
	addq	$32, %rsp
	popq	%rdi
	popq	%rsi
	ret
windows2linux_end:


/*
 * A Linux function calls this function, this function calls a Windows function
 *
 * The stack looks like
 * | Addr | Addr | Content | Pointer |
 * |------|------|---------|---------|
 * | 32   | 112  | arg10   |         |
 * | 24   | 104  | arg9    |         |
 * | 16   | 96   | arg8    |         |
 * | 8    | 88   | arg7    |         |
 * | 0    | 80   | return  | old rsp |
 * |      | 72   | arg10   |         |
 * |      | 64   | arg9    |         |
 * |      | 56   | arg8    |         |
 * |      | 48   | arg7    |         |
 * |      | 40   | arg6    |         |
 * |      | 32   | arg5    |         |
 * |      | 24   | (arg4)  |         |
 * |      | 16   | (arg3)  |         |
 * |      | 8    | (arg2)  |         |
 * |      | 0    | (arg1)  |         |
 */
.global linux2windows
.global linux2windows_call
.global linux2windows_call_end
.global linux2windows_end

linux2windows:
	pushq	32(%rsp)
	pushq	32(%rsp)
	pushq	32(%rsp)
	pushq	32(%rsp)
	pushq	%r9
	pushq	%r8
	movq	%rcx, %r9
	movq	%rdx, %r8
	movq	%rsi, %rdx
	movq	%rdi, %rcx
	pushq	%r9
	pushq	%r8
	pushq	%rdx
	pushq	%rcx
linux2windows_call:
	movq	$0xfedcba9876543210, %rax
linux2windows_call_end:
	call	*%rax
	addq	$80, %rsp
	ret
linux2windows_end:

