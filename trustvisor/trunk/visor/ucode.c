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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

#include <ucode.h>
#include <print.h>
#include <types.h>

static inline u32 cpuid_eax(u32 op)
{
    u32 eax;

    __asm__ __volatile__ ("cpuid"
                          : "=a" (eax)
                          : "0" (op)
                          : "bx", "cx", "dx");
    return eax;
}

static bool load_ucode(char *base, int size, uint32_t cpu_id)
{
    struct ucode_patch_hdr *uph = (struct ucode_patch_hdr *) base;
    uint32_t edx, eax, id;

    if(size < 0)
        return false;
    if ((u32)size < sizeof(*uph))
        return false;
    if (uph->processor_rev_id != cpu_id)
        return false;

    /* load microcode patch */
    edx = 0;
    eax = (uint32_t) &uph->data_code;
    asm volatile("wrmsr" :: "c" (0xc0010020), "a" (eax), "d" (edx));

    /* get patch id after patching */
    asm volatile("rdmsr" : "=a" (id) : "c" (0x0000008B));

    if (id == uph->patch_id) {
        printf("BSP: Loaded microcode patch ID %08x\n",
                uph->patch_id);
    } else {
        printf("BSP: Failed to load microcode patch\n");
    }

    return true;
}


/*
 * Load AMD-style microcode patch into BSP only.  When TrustVisor
 * becomes multi-core, we will need to call this function from each AP
 * as well.
 *
 * @ucode_addr points to a 32-bit length, followed immediately by that
 * many bytes of microcode patch.
 */
bool core_load_ucode(u32 ucode_addr)
{
    u32 current_cpu_id, equiv_cpu_id;
    struct ucode_equ_entry *equtab, *p;
    struct ucode_container_hdr *uch;
    int size, n;
    u8 *base;

    size = *((u32*)ucode_addr);
    base = (u8*)(ucode_addr+4);

    //printf("core_load_ucode: size %d, base 0x%x\n", size, (u32)base);
    
    if (size <= 0)
        return true;

    if(*((u32*)base) == UCODE_MAGIC) {
        base += sizeof(u32);
        size -= sizeof(u32);
    } else {
        printf("ERROR: *base 0x%x != UCODE_MAGIC 0x%x\n", *((u32*)base), UCODE_MAGIC);
        return false;
    }

    uch = (struct ucode_container_hdr *) base;
    
    if (uch->type != UCODE_EQUTAB) {
        printf("uch->type (0x%x) != UCODE_EQUTAB\n", (u32)uch->type);
        return false;
    }

    /* check the equivalency table for the cpu id */
    equiv_cpu_id = 0;
    current_cpu_id = cpuid_eax(0x00000001);

    n = uch->size / sizeof(struct ucode_equ_entry);
    equtab = (struct ucode_equ_entry *)(uch + 1);
    for (p = equtab; p < &equtab[n]; p++) {
        if (p->installed_cpu == current_cpu_id) {
            equiv_cpu_id = p->equiv_cpu;
            break;
        }
    }
    if (!equiv_cpu_id) {
        printf("Warning: BSP: ID %08x not found in equivalency table\n",
               current_cpu_id);
        return true;
    }

    size -= sizeof(struct ucode_container_hdr) + uch->size;
    base += sizeof(struct ucode_container_hdr) + uch->size;

    /* search for an applicable microcode patch */
    while (size > 0) {
        uch = (struct ucode_container_hdr *) base;
        if (uch->type != UCODE_PATCH) {
            printf("uch->type 0x%x != UCODE_PATCH 0x%x\n", uch->type, UCODE_PATCH);
            return false;
        }
        if (load_ucode((char *)(uch+1), uch->size, equiv_cpu_id))
            return true;

        size -= sizeof(struct ucode_container_hdr) + uch->size;
        base += sizeof(struct ucode_container_hdr) + uch->size;
    }

    return false;
}

