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

#include <xmhf.h>

#ifndef __XMHF_VERIFICATION__

#ifdef __AMD64__
	/*
	 * NOTE: in 64-bit mode, use (VA + 256MiB) % 4GiB = PA to access physical
	 *       memory.
	 */
	extern u32 xmhf_baseplatform_arch_flat_va_offset;
#elif !defined(__I386__)
    #error "Unsupported Arch"
#endif /* !defined(__I386__) */

	static inline void writeb(u32 addr, u8 val) {
#ifdef __AMD64__
		u32 phys_addr = (u32)addr - (u32)xmhf_baseplatform_arch_flat_va_offset;
		*(u8 *)(u64)phys_addr = val;
#elif defined(__I386__)
		__asm__ __volatile__("movb %%al, %%fs:(%%ebx)\r\n"
							 :
							 : "b"(addr), "a"((u32)val)
							 );
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
	}

	static inline u8 readb(u32 addr) {
#ifdef __AMD64__
		u32 phys_addr = (u32)addr - (u32)xmhf_baseplatform_arch_flat_va_offset;
		return *(u8 *)(u64)phys_addr;
#elif defined(__I386__)
		u32 ret;
		__asm__ __volatile("xor %%eax, %%eax\r\n"
						   "movb %%fs:(%%ebx), %%al\r\n"
						   : "=a"(ret)
						   : "b"(addr)
						   );
		return (u8)ret;
#else /* !defined(__I386__) && !defined(__AMD64__) */
    #error "Unsupported Arch"
#endif /* !defined(__I386__) && !defined(__AMD64__) */
	}

#else //__XMHF_VERIFICATION__

	static inline void writeb(u32 addr, u8 val) {

	}

	static inline u8 readb(u32 addr) {
	 return 0;
	}

#endif //__XMHF_VERIFICATION__

void _read_tpm_reg(int locality, u32 reg, u8 *_raw, size_t size)
{
    size_t i;
    for ( i = 0; i < size; i++ )
        _raw[i] = readb((TPM_LOCALITY_BASE_N(locality) | reg) + i);
}

void _write_tpm_reg(int locality, u32 reg, u8 *_raw, size_t size)
{
    size_t i;
    for ( i = 0; i < size; i++ )
        writeb((TPM_LOCALITY_BASE_N(locality) | reg) + i, _raw[i]);
}

void copy_hash(tb_hash_t *dest_hash, const tb_hash_t *src_hash,
               uint16_t hash_alg)
{
    unsigned int len;

    if ( dest_hash == NULL || src_hash == NULL ) {
        printf("hashes are NULL\n");
        return;
    }

    len = get_hash_size(hash_alg);
    if ( len > 0 )
        memcpy(dest_hash, src_hash, len);
    else
        printf("unsupported hash alg (%u)\n", hash_alg);
}


//======================================================================
//ARCH. Backends
//======================================================================

//deactivate all TPM localities
void xmhf_tpm_arch_deactivate_all_localities(void) {
    tpm_reg_access_t reg_acc;
    uint32_t locality;

    printf("\nTPM: %s()\n", __FUNCTION__);
    for(locality=0; locality <= 3; locality++) {
        reg_acc._raw[0] = 0;
        reg_acc.active_locality = 1;
        write_tpm_reg(locality, TPM_REG_ACCESS, &reg_acc);
    }
}

//open TPM locality
int xmhf_tpm_arch_open_locality(int locality){
    u32 cpu_vendor = get_cpu_vendor_or_die();

    if(cpu_vendor == CPU_VENDOR_INTEL) {
        return xmhf_tpm_arch_x86vmx_open_locality(locality);
    } else { /* AMD */
        return xmhf_tpm_arch_x86svm_open_locality(locality);
    }
}
