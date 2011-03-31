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

/* ==========================================
    CMock Project - Automatic Mock Generation for C
    Copyright (c) 2007 Mike Karlesky, Mark VanderVoord, Greg Williams
    [Released under MIT License. Please refer to license.txt for details]
========================================== */

typedef unsigned short U16;
typedef signed int int32_t;

typedef struct _POINT_T
{
  int x;
  int y;
} POINT_T;

// typedef edge case;
// not ANSI C but it has been done and will break cmock if not handled
typedef void VOID_TYPE_CRAZINESS;

/* fun parsing & mock generation cases */

void var_args1(int a, ...);
void var_args2(int a, int b, ...);

VOID_TYPE_CRAZINESS void_type_craziness1(int, float, double, char, short, long, long int, long long, void*);
int void_type_craziness2( VOID_TYPE_CRAZINESS );

   void  crazy_whitespace  (   int    lint, double shot  ,  short  stack )  ;

char
 crazy_multiline
(
  int a,
  unsigned int b);

U16  *ptr_return1(int a);
U16*  ptr_return2(int a);
U16 * ptr_return3(int a);

unsigned int** ptr_ptr_return1(unsigned int** a);
unsigned int* *ptr_ptr_return2(unsigned int* *a);
unsigned int **ptr_ptr_return3(unsigned int **a);
unsigned int ** ptr_ptr_return4(unsigned int ** a);

extern unsigned long int incredible_descriptors(register const unsigned short a);

int32_t example_c99_type(int32_t param1);
