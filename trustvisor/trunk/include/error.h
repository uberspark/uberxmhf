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

/* error.h simple error handling macros 
 * Modiifed from Xen for TrustVisor by Elaine Shi and Arvind Seshadri
 */

#ifndef __ERROR_H_
#define __ERROR_H_

#ifndef __ASSEMBLY__

extern u32 debug_flag;
#define DEBUG if ( debug_flag )

#define EARLY_FAIL() for(;;) __asm__ __volatile__("hlt")

#if 1
#define FORCE_CRASH() do {				\
    printf("DEBUG: Crash at %s:%d\n", __FILE__, __LINE__);	\
    __asm__ __volatile__ ( "1: jmp 1b" );			\
} while (0);
#define FORCE_REBOOT() do {				\
    printf("DEBUG: Crash at %s:%d, Rebooting ...\n", __FILE__, __LINE__);	\
    __asm__ __volatile__ ( "ud2" );			\
} while (0);
#else
#define FORCE_CRASH() do {				\
    printf("DEBUG: Crash at %s:%d\n", __FILE__, __LINE__);	\
    __asm__ __volatile__ ( "ud2" );			\
} while (0);
#define FORCE_REBOOT() do {				\
    printf("DEBUG: Crash at %s:%d, Rebooting ...\n", __FILE__, __LINE__);	\
    __asm__ __volatile__ ( "ud2" );			\
} while (0);
#endif

#define BUG() do {					\
    printf("BUG at %s:%d\n", __FILE__, __LINE__);	\
    FORCE_CRASH();                                      \
} while ( 0 )

#define BUG_ON(_p) do { if (_p) BUG(); } while ( 0 )

#define ASSERT(_p) { if ( !(_p) ) { printf("Assertion '%s' failed, line %d, file %s\n", #_p , __LINE__, __FILE__); BUG(); } }

#endif /*__ASSEMBLY__*/


#endif /* _ERROR_H */
