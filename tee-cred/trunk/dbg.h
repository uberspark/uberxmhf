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

/*
 * From 'Learn C The Hard Way' by Zed Shaw
 * http://c.learncodethehardway.org/book/learn-c-the-hard-waych21.html#x26-10500021
 */

#ifndef __dbg_h__
#define __dbg_h__
  
#include <stdio.h>
#include <errno.h> 
#include <string.h>
  
#define MAP1(x, f1, t1, d) (((x)==(f1)) ? (t1) : (d))
#define MAP2(x, f1, t1, f2, t2, d) MAP1(x, f1, t1, (((x)==(f2)) ? (t2) : (d)))
#define MAP3(x, f1, t1, f2, t2, f3, t3, d) MAP2(x, f1, t1, f2, t2, (((x)==(f3)) ? (t3) : (d)))

#ifdef NDEBUG
#define debug(M, ...)
#else 
#define debug(M, ...) fprintf(stderr, "DEBUG %s:%d: " M "\n", __FILE__, __LINE__, ##__VA_ARGS__) 
#endif
  
#define clean_errno() (errno == 0 ? "None" : strerror(errno))
   
#define log_err(M, ...) fprintf(stderr, "[ERROR] (%s:%d: errno: %s) " M "\n", __FILE__, __LINE__, clean_errno(), ##__VA_ARGS__) 
#define log_err_rv(M, RV, ...) fprintf(stderr, "[ERROR] (%s:%d: rv: 0x%x) " M "\n", __FILE__, __LINE__, RV, ##__VA_ARGS__) 
   
#define log_warn(M, ...) fprintf(stderr, "[WARN] (%s:%d: errno: %s) " M "\n", __FILE__, __LINE__, clean_errno(), ##__VA_ARGS__) 
   
#define log_info(M, ...) fprintf(stderr, "[INFO] (%s:%d) " M "\n", __FILE__, __LINE__, ##__VA_ARGS__) 
  
#define check(A, M, ...) if(!(A)) { log_err(M, ##__VA_ARGS__); errno=0; goto error; } 

#define CHECK(A, NEWRV, M, ...) if(!(A)) { log_err(M, ##__VA_ARGS__); rv=(NEWRV); goto out; } 
#define CHECK_MEM(A, NEWRV) if(!(A)) { log_err("Out of memory."); rv=(NEWRV); goto out; } 
#define CHECK_RV(RV, NEWRV, M, ...) if((RV)) { log_err_rv(M, RV, ##__VA_ARGS__); rv=(NEWRV); goto out; } 
#define CHECK_2RV(RV, NEWRV, RV2, NEWRV2, M, ...) CHECK_RV(RV, NEWRV, M " (RV1)", ##__VA_ARGS__); CHECK_RV(RV2, NEWRV2, M " (RV2)", ##__VA_ARGS__)
#define CHECK_3RV(RV, NEWRV, RV2, NEWRV2, RV3, NEWRV3, M, ...) CHECK_2RV(RV, NEWRV, RV2, NEWRV2, M, ##__VA_ARGS__); CHECK_RV(RV3, NEWRV3, M " (RV3)", ##__VA_ARGS__)

#define sentinel(M, ...)  { log_err(M, ##__VA_ARGS__); errno=0; goto error; } 
  
#define check_mem(A) check((A), "Out of memory.")
   
#define check_debug(A, M, ...) if(!(A)) { debug(M, ##__VA_ARGS__); errno=0; goto error; } 
  
#endif
