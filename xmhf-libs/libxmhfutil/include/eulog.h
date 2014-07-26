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

#ifndef EULOG_H
#define EULOG_H

#define EU_TRACE 0
#define EU_PERF  1
#define EU_WARN  2
#define EU_ERR   3

#ifndef EU_LOG_PREFIX
#define EU_LOG_PREFIX ""
#endif

#ifndef EU_LOG_LVL
#define EU_LOG_LVL EU_TRACE
#endif

#ifndef EU_LOG_PRINTLN
#define EU_LOG_PRINTLN( prefix, fmt, args...) printf( "%-50s " fmt "\n", prefix, ## args)
#endif

#include <stdio.h>
#include <stdarg.h>

#ifndef EU_PREFIX_MAX_LEN
#define EU_PREFIX_MAX_LEN 256
#endif

#define EU_LOG(pri, fmt, args...)                                        \
  do {                                                                  \
    char _eulogbuf[EU_PREFIX_MAX_LEN];                                                \
    if (EU_LOG_LVL <= pri) {                                             \
      snprintf(_eulogbuf, EU_PREFIX_MAX_LEN, "%s[%d]:%s:%s:%d:", EU_LOG_PREFIX, pri, __FILE__, __FUNCTION__, __LINE__); \
      _eulogbuf[EU_PREFIX_MAX_LEN-1] = '\0';                                            \
      EU_LOG_PRINTLN( _eulogbuf, fmt, ## args);                         \
    }                                                                   \
  } while(0)

#define eu_trace(fmt, args...) EU_LOG(EU_TRACE, fmt, ## args)
#define eu_perf(fmt, args...) EU_LOG(EU_PERF, fmt, ## args)
#define eu_warn(fmt, args...) EU_LOG(EU_WARN, fmt, ## args)
#define eu_err(fmt, args...) EU_LOG(EU_ERR, fmt, ## args)

#define eu_pulse() EU_LOG(EU_TRACE, "pulse")

/* below are versions that can be used where an expression is
   expected. this is useful as extra parameters to eu_chk
   functions. Unfortunately we end up using multiple print statements,
   which may not be printed atomically.
*/
static int eu_logfn(const char* fmt, const char* prefix, int pri, const char *file, const char *fn, int line, ...) __attribute__ ((unused));
static int eu_logfn(const char* fmt, const char* prefix, int pri, const char *file, const char *fn, int line, ...)
{
  va_list va;
  char loc_string[128];
  /* int written; */

  snprintf(loc_string, 128, "%s[%d]:%s:%s:%d:", prefix, pri, file, fn, line);
  printf("%-50s ", loc_string);

  va_start(va, line);
  vprintf(fmt, va);
  va_end(va);

  printf("\n");
  return 0;
}

#define EU_LOGE(pri, fmt, args...)                                      \
  ((void)((EU_LOG_LVL <= pri) &&                                        \
          eu_logfn(fmt, EU_LOG_PREFIX, pri, __FILE__, __FUNCTION__, __LINE__, ## args)))

#define eu_trace_e(fmt, args...) EU_LOGE(EU_TRACE, fmt, ## args)
#define eu_perf_e(fmt, args...) EU_LOGE(EU_PERF, fmt, ## args)
#define eu_warn_e(fmt, args...) EU_LOGE(EU_WARN, fmt, ## args)
#define eu_err_e(fmt, args...) EU_LOGE(EU_ERR, fmt, ## args)

#define eu_pulse_e() EU_LOGE(EU_TRACE, "pulse"

#endif
