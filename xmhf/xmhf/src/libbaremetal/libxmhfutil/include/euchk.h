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

#ifndef EUCHK_H
#define EUCHK_H

#include <eulog.h>
#include <stdlib.h>

/* normally use eu_log, but give option for client to override */
#ifndef EU_CHK_LOG
#define EU_CHK_LOG( pri, fmt, args...) EU_LOG( pri, fmt, ## args)
#endif

/* EU_CHK(cond) - if condition is false, will log an error, including
 * the stringified condition, and goto label 'out'. Use above variants
 * if a different logging priority is desired.
 *
 * Optionally, include additional expressions that will be evaluated
 * iff the condition doesn't hold.  This can be used, e.g., to set a
 * return value or error flag.  examples:
 * 
 * EU_CHK((buf = malloc(20)));
 *
 * EU_CHK(buf = malloc(20),
 *        rv = ENOMEM);
 *
 * In either case, allocation failure will print a useful log message
 * including the location of the check and the stringified condition
 * that failed ("buf = malloc(20)"), and goto label 'out'. In the
 * second case, failure will also cause the variable rv to be assigned
 * ENOMEM.
 *
 * EU_CHKN is as-above, but inverts the condition, and prints the value of the condition
 * on failure. useful for checking (and printing) error codes. example:
 *
 * EU_CHKN(fn_that_may_fail(arg1, arg2, arg3));
 *
 * if fn_that_may_fail returns non-zero, the check will fail and the
 * return value will be logged.
 *
 */ 

#define EU_CHKN_PRI(cond, priority, args...)                            \
  do {                                                                  \
    int _eu_chk_cond = (int)(cond);                                     \
    if (_eu_chk_cond) {                                                 \
      EU_CHK_LOG(priority, "EU_CHKN( %s) failed with: %d", #cond, _eu_chk_cond); \
      (void)0, ## args;                                                 \
      goto out;                                                         \
    }                                                                   \
  } while(0)

#define EU_CHK_PRI(cond, priority, args...)             \
  do {                                                  \
    if (!(cond)) {                                      \
      EU_CHK_LOG(priority, "EU_CHK( %s) failed", #cond);    \
      (void)0, ## args;                                 \
      goto out;                                         \
    }                                                   \
  } while(0)

#define EU_CHK_T(cond, args...) EU_CHK_PRI(cond, EU_TRACE, ## args)
#define EU_CHK_W(cond, args...) EU_CHK_PRI(cond, EU_WARN, ## args)
#define EU_CHK_E(cond, args...) EU_CHK_PRI(cond, EU_ERR, ## args)

#define EU_CHKN_T(cond, args...) EU_CHKN_PRI(cond, EU_TRACE, ## args)
#define EU_CHKN_W(cond, args...) EU_CHKN_PRI(cond, EU_WARN, ## args)
#define EU_CHKN_E(cond, args...) EU_CHKN_PRI(cond, EU_ERR, ## args)

#define EU_CHK(cond, args...) EU_CHK_E(cond, ## args)
#define EU_CHKN(cond, args...) EU_CHKN_E(cond, ## args)

/* use like assert, but where arg will always be expanded and the
   check never disabled */
#define EU_VERIFY(cond, args...)                \
  do {                                          \
    if (!(cond)) {                              \
      EU_CHK_LOG( EU_ERR, "EU_VERIFY( %s) failed", #cond);       \
      (void)0, ## args;                         \
      abort();                                  \
    }                                           \
  } while(0)

/* verify-not. logs value in case of failure as with EU_CHKN. */
#define EU_VERIFYN(cond, args...)                                       \
  do {                                                                  \
    int _eu_chk_cond = (int)(cond);                                     \
    if (_eu_chk_cond) {                                                 \
      EU_CHK_LOG( EU_ERR, "EU_VERIFYN( %s) failed with %d", #cond, _eu_chk_cond); \
      (void)0, ## args;                                                 \
      abort();                                                          \
    }                                                                   \
  } while(0)

#endif
