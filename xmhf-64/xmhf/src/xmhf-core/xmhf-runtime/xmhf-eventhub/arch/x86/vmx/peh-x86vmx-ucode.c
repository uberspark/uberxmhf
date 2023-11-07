/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

// peh-x86vmx-ucode.c
// Handle Intel microcode update
// author: Eric Li (xiaoyili@andrew.cmu.edu)
#include <xmhf.h>

#include <hptw.h>
#include <hpt_emhf.h>

extern unsigned char ucode_recognized_sha1s[][SHA_DIGEST_LENGTH];
extern u32 ucode_recognized_sha1s_len;

/*
 * Maximum supported microcode size. For some CPUs this may need to be much
 * larger (e.g. > 256K).
 */
#define UCODE_TOTAL_SIZE_MAX (PAGE_SIZE_4K)

/* Space to temporarily copy microcode update (prevent TOCTOU attack) */
static u8 ucode_copy_area[MAX_VCPU_ENTRIES * UCODE_TOTAL_SIZE_MAX]
__attribute__(( section(".bss.palign_data") ));

typedef struct __attribute__ ((packed)) {
	u32 header_version;
	u32 update_version;
	u32 date;
	u32 processor_signature;
	u32 checksum;
	u32 loader_version;
	u32 processor_flags;
	u32 data_size;
	u32 total_size;
	u32 reserved[3];
	u8 update_data[0];
} intel_ucode_update_t;

typedef struct __attribute__ ((packed)) {
	u32 processor_signature;
	u32 processor_flags;
	u32 checksum;
} intel_ucode_ext_sign_t;

typedef struct __attribute__ ((packed)) {
	u32 extended_signature_count;
	u32 extended_processor_signature_table_checksum;
	u32 reserved[3];
	intel_ucode_ext_sign_t signatures[0];
} intel_ucode_ext_sign_table_t;

typedef struct {
	hptw_ctx_t guest_ctx;
	hptw_ctx_t host_ctx;
} ucode_hptw_ctx_pair_t;

static hpt_pa_t ucode_host_ctx_ptr2pa(void *vctx, void *ptr)
{
	(void)vctx;
	return hva2spa(ptr);
}

static void* ucode_host_ctx_pa2ptr(void *vctx, hpt_pa_t spa, size_t sz, hpt_prot_t access_type, hptw_cpl_t cpl, size_t *avail_sz)
{
	(void)vctx;
	(void)access_type;
	(void)cpl;
	*avail_sz = sz;
	return spa2hva(spa);
}

static hpt_pa_t ucode_guest_ctx_ptr2pa(void __attribute__((unused)) *ctx, void *ptr)
{
	return hva2gpa(ptr);
}

static void* ucode_guest_ctx_pa2ptr(void *vctx, hpt_pa_t gpa, size_t sz, hpt_prot_t access_type, hptw_cpl_t cpl, size_t *avail_sz)
{
	ucode_hptw_ctx_pair_t *ctx_pair = vctx;

	return hptw_checked_access_va(&ctx_pair->host_ctx,
									access_type,
									cpl,
									gpa,
									sz,
									avail_sz);
}

static void* ucode_ctx_unimplemented(void *vctx, size_t alignment, size_t sz)
{
	(void)vctx;
	(void)alignment;
	(void)sz;
	HALT_ON_ERRORCOND(0 && "Not implemented");
	return NULL;
}

/*
 * Check SHA-1 hash of the update
 * Return 1 if the update is recognized, 0 otherwise
 */
static int ucode_check_sha1(intel_ucode_update_t *header)
{
	const unsigned char *buffer = (const unsigned char *) header;
	unsigned char md[SHA_DIGEST_LENGTH];
	HALT_ON_ERRORCOND(sha1_buffer(buffer, header->total_size, md) == 0);
	print_hex("SHA1(update) = ", md, SHA_DIGEST_LENGTH);
	for (u32 i = 0; i < ucode_recognized_sha1s_len; i++) {
		if (memcmp(md, ucode_recognized_sha1s[i], SHA_DIGEST_LENGTH) == 0) {
			return 1;
		}
	}
	return 0;
}

/*
 * Check the processor flags of the update
 * Return 1 if the update is for this processor, 0 otherwise
 */
static int ucode_check_processor_flags(u32 processor_flags)
{
	u64 flag = 1 << ((rdmsr64(IA32_PLATFORM_ID) >> 50) & 0x7);
	return !!(processor_flags & flag);
}

/*
 * Check the processor signature and processor flags of the update
 * Return 1 if the update is for this processor, 0 otherwise
 */
static int ucode_check_processor(intel_ucode_update_t *header)
{
	u32 eax, ebx, ecx, edx;
	cpuid(1, &eax, &ebx, &ecx, &edx);
	HALT_ON_ERRORCOND(header->header_version == 1);
	if (header->processor_signature == eax) {
		return ucode_check_processor_flags(header->processor_flags);
	} else if (header->total_size > header->data_size + 48) {
		intel_ucode_ext_sign_table_t *ext_sign_table;
		u32 n;
		u32 ext_size = header->total_size - (header->data_size + 48);
		HALT_ON_ERRORCOND(ext_size >= sizeof(intel_ucode_ext_sign_table_t));
		ext_sign_table = ((void *) header) + (header->data_size + 48);
		n = ext_sign_table->extended_signature_count;
		HALT_ON_ERRORCOND(ext_size >= sizeof(intel_ucode_ext_sign_table_t) +
							n * sizeof(intel_ucode_ext_sign_t));
		for (u32 i = 0; i < n; i++) {
			intel_ucode_ext_sign_t *signature = &ext_sign_table->signatures[i];
			if (signature->processor_signature == eax) {
				return ucode_check_processor_flags(signature->processor_flags);
			}
		}
	}
	return 0;
}

/*
 * Update microcode.
 * This function should be called when handling WRMSR to IA32_BIOS_UPDT_TRIG.
 * update_data should be EDX:EAX, which is the guest virtual address of "Update
 * Data". The header and other metadata (e.g. size) starts at 48 bytes before
 * this address.
 */
void handle_intel_ucode_update(VCPU *vcpu, u64 update_data)
{
	hpt_type_t guest_t = hpt_emhf_get_guest_hpt_type(vcpu);
	ucode_hptw_ctx_pair_t ctx_pair = {
		.guest_ctx = {
			.ptr2pa = ucode_guest_ctx_ptr2pa,
			.pa2ptr = ucode_guest_ctx_pa2ptr,
			.gzp = ucode_ctx_unimplemented,
			.root_pa = hpt_cr3_get_address(guest_t, vcpu->vmcs.guest_CR3),
			.t = guest_t,
		},
		.host_ctx = {
			.ptr2pa = ucode_host_ctx_ptr2pa,
			.pa2ptr = ucode_host_ctx_pa2ptr,
			.gzp = ucode_ctx_unimplemented,
			.root_pa = hpt_eptp_get_address(HPT_TYPE_EPT,
											vcpu->vmcs.control_EPT_pointer),
			.t = HPT_TYPE_EPT,
		}
	};
	hptw_ctx_t *ctx = &ctx_pair.guest_ctx;
	u64 va_header = update_data - sizeof(intel_ucode_update_t);
	u8 *copy_area;
	intel_ucode_update_t *header;
	int result;
	size_t size;
	HALT_ON_ERRORCOND(vcpu->idx < UCODE_TOTAL_SIZE_MAX);
	copy_area = ucode_copy_area + UCODE_TOTAL_SIZE_MAX * vcpu->idx;
	/* Copy header of microcode update */
	header = (intel_ucode_update_t *) copy_area;
	size = sizeof(intel_ucode_update_t);
	result = hptw_checked_copy_from_va(ctx, 0, header, va_header, size);
	HALT_ON_ERRORCOND(result == 0);
	printf("\nCPU(0x%02x): date(mmddyyyy)=%08x, dsize=%d, tsize=%d",
			vcpu->id, header->date, header->data_size, header->total_size);
	/* If the following check fails, increase UCODE_TOTAL_SIZE_MAX */
	HALT_ON_ERRORCOND(header->total_size <= UCODE_TOTAL_SIZE_MAX);
	/* Copy the rest of of microcode update */
	size = header->total_size - size;
	result = hptw_checked_copy_from_va(ctx, 0, &header->update_data,
										update_data, size);
	/* Check the hash of the update */
	if (!ucode_check_sha1(header)) {
		printf("\nCPU(0x%02x): Unrecognized microcode update, HALT!", vcpu->id);
		HALT();
	}
	/* Check whether update is for the processor */
	if (!ucode_check_processor(header)) {
		printf("\nCPU(0x%02x): Incompatible microcode update, HALT!", vcpu->id);
		HALT();
	}
	/*
	for (u32 i = 0; i < header->total_size; i++) {
		if (i % 16 == 0) {
			printf("\n%08x  ", i);
		} else if (i % 8 == 0) {
			printf("  ");
		} else {
			printf(" ");
		}
		printf("%02x", copy_area[i]);
	}
	*/
	/* Forward microcode update to host */
	printf("\nCPU(0x%02x): Calling physical ucode update at 0x%08lx",
			vcpu->id, &header->update_data);
	wrmsr64(IA32_BIOS_UPDT_TRIG, (uintptr_t) &header->update_data);
	printf("\nCPU(0x%02x): Physical ucode update returned", vcpu->id);
}

