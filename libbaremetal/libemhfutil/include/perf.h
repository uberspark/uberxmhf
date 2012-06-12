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

/* perf.h - profiling utility functions
 * 
 * author - Jim Newsome (jnewsome@no-fuss.com)
 *
 * Some utility functions for profiling. They are designed to be
 * smp-safe - each running timer is cpu-specific.
 *
 * Call perf_ctr_init before using a perf_ctr_t.
 * Call perf_ctr_timer_start before
 *   perf_ctr_timer_record or perf_ctr_timer_discard.
 * After calling perf_ctr_timer_start, be sure to call
 *   perf_ctr_timer_record or perf_ctr_timer_discard before calling it again
 */

#ifndef PERF_H
#define PERF_H

#ifndef __ASSEMBLY__


#ifdef __PROFILING__

typedef struct perf_counter {
  /* per-cpu */
  u64 start_time[MAX_VCPU_ENTRIES];

  /* protects all below */
  u32 lock;

  u64 total_time;
  u64 count;
} perf_ctr_t;

/* call exactly once for a perf_ctr_t */
static inline void perf_ctr_init(perf_ctr_t *p)
{
  u32 i;

  for(i=0; i<MAX_VCPU_ENTRIES; i++) {
    p->start_time[i] = 0;
  }
  p->lock = 1;
  p->total_time = 0;
  p->count = 0;
}

/* ASSUMES no currently running timers in p. */
static inline void perf_ctr_reset(perf_ctr_t *p)
{
  u32 i;
  spin_lock(&(p->lock));
  for(i=0; i<MAX_VCPU_ENTRIES; i++) {
    ASSERT(p->start_time[i] == 0);
  }
  p->total_time = 0;
  p->count = 0;
  spin_unlock(&(p->lock));
}

/* p must be initialized, and the specified timer not running */
static inline void perf_ctr_timer_start(perf_ctr_t *p, u32 cpuid)
{
  ASSERT(cpuid < MAX_VCPU_ENTRIES);
  ASSERT(p->start_time[cpuid] == 0);

  p->start_time[cpuid] = rdtsc64();
}

/* specified timer must be running */
static inline void perf_ctr_timer_record(perf_ctr_t *p, u32 cpuid)
{
  ASSERT(cpuid < MAX_VCPU_ENTRIES);
  ASSERT(p->start_time[cpuid] != 0);

  spin_lock(&(p->lock));
  p->total_time += rdtsc64() - p->start_time[cpuid];
  p->count++;
  p->start_time[cpuid] = 0;
  spin_unlock(&(p->lock));
}

/* specified timer must be running */
static inline void perf_ctr_timer_discard(perf_ctr_t *p, u32 cpuid)
{
  ASSERT(cpuid < MAX_VCPU_ENTRIES);
  ASSERT(p->start_time[cpuid] != 0);

  p->start_time[cpuid] = 0;
}

static inline u64 perf_ctr_get_total_time(perf_ctr_t *p)
{
  u64 rv;
  spin_lock(&(p->lock));
  rv = p->total_time;
  spin_unlock(&(p->lock));
  return rv;
}

static inline u64 perf_ctr_get_count(perf_ctr_t *p)
{
  u64 rv;
  spin_lock(&(p->lock));
  rv = p->count;
  spin_unlock(&(p->lock));
  return rv;
}

#else /* __PROFILING__ */

typedef struct perf_counter {
	u32 placeholder;
} perf_ctr_t;

/* call exactly once for a perf_ctr_t */
#define perf_ctr_init(...) do { } while (0)
#define perf_ctr_reset(...) do { } while (0)
#define perf_ctr_timer_start(...) do { } while (0)
#define perf_ctr_timer_record(...) do { } while (0)
#define perf_ctr_timer_discard(...) do { } while (0)
#define perf_ctr_get_total_time(...) 0ull
#define perf_ctr_get_count(...) 0ull



#endif /* __PROFILING__ */


#endif //__ASSEMBLY__


#endif
