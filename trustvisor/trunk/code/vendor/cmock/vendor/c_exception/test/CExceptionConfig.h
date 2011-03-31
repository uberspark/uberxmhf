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

#ifndef _EXCEPTION_H
#define _EXCEPTION_H

//Optionally define the exception type (something like an int which can be directly assigned)
#define CEXCEPTION_T    int

// Optionally define the reserved value representing NO EXCEPTION
#define CEXCEPTION_NONE (1234)

// Multi-Tasking environments will need a couple of macros defined to make this library 
// properly handle  multiple exception stacks.  You will need to include and required
// definitions, then define the following macros:
//    EXCEPTION_GET_ID - returns the id of the current task indexed 0 to (numtasks - 1)
//    EXCEPTION_NUM_ID - returns the number of tasks that might be returned
//
// For example, Quadros might include the following implementation:
#ifndef TEST
#include "OSAPI.h"
#define CEXCEPTION_GET_ID    (KS_GetTaskID())
#define CEXCEPTION_NUM_ID    (NTASKS + 1)
#endif

//This could be a good place to define/include some error ID's:
#define ERROR_ID_EVERYTHING_IS_BROKEN  (0x88)
#define ERROR_ID_ONLY_THIS_IS_BROKEN   (0x77)

#endif // _EXCEPTION_H
