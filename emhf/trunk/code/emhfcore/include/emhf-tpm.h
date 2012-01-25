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

// EMHF TPM component declarations
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EMHF_TPM_H__
#define __EMHF_TPM_H__


#ifndef __ASSEMBLY__


//----------------------------------------------------------------------
//exported DATA 
//----------------------------------------------------------------------


//----------------------------------------------------------------------
//exported FUNCTIONS 
//----------------------------------------------------------------------

//open TPM locality
int emhf_tpm_open_locality(int locality);

//check if TPM is ready for use
bool emhf_tpm_is_tpm_ready(uint32_t locality);

//----------------------------------------------------------------------
//ARCH. BACKENDS
//----------------------------------------------------------------------

//open TPM locality
int emhf_tpm_arch_open_locality(int locality);

//check if TPM is ready for use
bool emhf_tpm_arch_is_tpm_ready(uint32_t locality);


//----------------------------------------------------------------------
//x86 ARCH. INTERFACES
//----------------------------------------------------------------------

/*********************************************************************
 * Moved in from tboot's tpm.c; I think it belongs in a .h file. Also
 * facilitates split into tpm.c and tpm_extra.c.
 *********************************************************************/

/* TODO: Give these a more appropriate home */
/* #define readb(va)       (*(volatile uint8_t *) (va)) */
/* #define writeb(va, d)   (*(volatile uint8_t *) (va) = (d)) */

#ifndef __EMHF_VERIFICATION__
static inline void writeb(u32 addr, u8 val) {
    __asm__ __volatile__("movb %%al, %%fs:(%%ebx)\r\n"
                         :
                         : "b"(addr), "a"((u32)val)
                         );
}

static inline u8 readb(u32 addr) {
    u32 ret;
    __asm__ __volatile("xor %%eax, %%eax\r\n"        
                       "movb %%fs:(%%ebx), %%al\r\n"
                       : "=a"(ret)
                       : "b"(addr)
                       );
    return (u8)ret;        
}
#endif	//__EMHF_VERIFICATION__


//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
//open TPM locality
int emhf_tpm_arch_x86vmx_open_locality(int locality);


//----------------------------------------------------------------------
//x86vmx SUBARCH. INTERFACES
//----------------------------------------------------------------------
//open TPM locality
int emhf_tpm_arch_x86svm_open_locality(int locality);


#endif	//__ASSEMBLY__

#endif //__EMHF_TPM_H__

