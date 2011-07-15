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

#include "unity.h"

#define __PRINT_H_ /* avoid indirectly including our print.h, which conflicts with libc stdio.h */

#define dprintf(...) while(0)

#define _PUTTYMEM_H_ /* avoid using puttymem */

#include <com.h> /* required by target.h included from drbg.h FIXME */
#include <drbg.h>

/* replacements for puttymem */
void *safemalloc(size_t size) {
    unsigned u = malloc(size);
    void *r = (void*)u;
    return r;
}

void safefree(void *p) {
    free(p);
}

void *vmemcpy(void *dest, const void *src, size_t n) {
    return memcpy(dest, src, n);
}

void *vmemset(void *s, int c, size_t n) {
    return memset(s, c, n);
}



/* standard unity constructions */
void setUp(void)
{
}

void tearDown(void)
{
}

/* actual tests */

#define maxu64 0xffffffffffffffffull

void test_ZERO_HI64(void)
{
  TEST_ASSERT_EQUAL_HEX64(maxu64, ZERO_HI64(maxu64, 0));
  TEST_ASSERT_EQUAL_HEX64(0x7fffffffffffffffull, ZERO_HI64(maxu64, 1));
  TEST_ASSERT_EQUAL_HEX64(0x1ull, ZERO_HI64(maxu64, 63));
}

void test_add1_INT128(void) {
    INT128 i;
    i.high = 0;
    i.low = maxu64;

    TEST_ASSERT_EQUAL_HEX64(maxu64, i.low);
    i.low++;
    TEST_ASSERT_EQUAL_HEX64(maxu64, i.low);

}
