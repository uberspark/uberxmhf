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

#ifndef EULOG_H
#define EULOG_H

#define EUTRACE 0
#define EUPERF  1
#define EUWARN  2
#define EUERR   3

#ifndef EULOG_PREFIX
#define EULOG_PREFIX ""
#endif

#ifndef EULOG_LVL
#define EULOG_LVL EUTRACE
#endif

#include <stdio.h>

#define EULOG(pri, fmt, args...)                                        \
  do {                                                                  \
    char _eulogbuf[128];                                                \
    if (EULOG_LVL <= pri) {                                             \
      snprintf(_eulogbuf, 128, "%s[%d]:%s:%s:%d:", EULOG_PREFIX, pri, __FILE__, __FUNCTION__, __LINE__); \
      _eulogbuf[127] = '\0';                                            \
      printf("%-50s " fmt "\n", _eulogbuf, ## args);                    \
    }                                                                   \
  } while(0)

      /* printf("%s[%d]:%s:%s:%d:\t" fmt "\n", EULOG_PREFIX, pri, __FILE__, __FUNCTION__, __LINE__, ## args); \ */

#define eutrace(fmt, args...) EULOG(EUTRACE, fmt, ## args)
#define euperf(fmt, args...) EULOG(EUPERF, fmt, ## args)
#define euwarn(fmt, args...) EULOG(EUWARN, fmt, ## args)
#define euerr(fmt, args...) EULOG(EUERR, fmt, ## args)

#define eupulse() EULOG(EUTRACE, "pulse")

#endif
