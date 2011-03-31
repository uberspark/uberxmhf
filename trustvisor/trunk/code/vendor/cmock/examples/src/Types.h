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

#ifndef _MYTYPES_H_
#define _MYTYPES_H_

#include "AT91SAM7X256.h"
#include <math.h>

#ifndef __monitor
#define __monitor
#endif

// Peripheral Helper Definitions
#define USART0_CLOCK_ENABLE (AT91C_ID_US0)
#define USART0_TX_PIN       (AT91C_PA1_TXD0)
#define TIMER0_CLOCK_ENABLE (((uint32)0x1) << AT91C_ID_TC0)
#define PIOA_CLOCK_ENABLE   (((uint32)0x1) << AT91C_ID_PIOA)
#define PIOB_CLOCK_ENABLE   (((uint32)0x1) << AT91C_ID_PIOB)
#define TIOA0_PIN_MASK      (((uint32)0x1) << 23) // Timer/Counter Output Pin

// Application Type Definitions
typedef unsigned int uint32;
typedef int int32;
typedef unsigned short uint16;
typedef short int16;
typedef unsigned char uint8;
typedef char int8;
typedef char bool;

// Application Special Value Definitions
#ifndef TRUE
#define TRUE      (1)
#endif
#ifndef FALSE
#define FALSE     (0)
#endif
#ifndef NULL
#define NULL      (0)
#endif // NULL
#define DONT_CARE (0)

#ifndef INFINITY
#define INFINITY (1.0 / 0.0)
#endif

#ifndef NAN
#define NAN (0.0 / 0.0)
#endif

// MIN/MAX Definitions for Standard Types
#ifndef INT8_MAX
#define INT8_MAX 127
#endif

#ifndef INT8_MIN
#define INT8_MIN (-128)
#endif

#ifndef UINT8_MAX
#define UINT8_MAX 0xFFU
#endif

#ifndef UINT8_MIN
#define UINT8_MIN 0x00U
#endif

#ifndef INT16_MAX
#define INT16_MAX 32767
#endif

#ifndef INT16_MIN
#define INT16_MIN (-32768)
#endif

#ifndef UINT16_MAX
#define UINT16_MAX 0xFFFFU
#endif

#ifndef UINT16_MIN
#define UINT16_MIN 0x0000U
#endif

#ifndef INT32_MAX
#define INT32_MAX 0x7FFFFFFF
#endif

#ifndef INT32_MIN
#define INT32_MIN (-INT32_MAX - 1)
#endif

#ifndef UINT32_MAX
#define UINT32_MAX 0xFFFFFFFFU
#endif

#ifndef UINT32_MIN
#define UINT32_MIN 0x00000000U
#endif

typedef struct _EXAMPLE_STRUCT_T
{
    int x;
    int y;
} EXAMPLE_STRUCT_T;

#endif // _MYTYPES_H_
