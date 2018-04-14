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

/**
 * malloc.[ch] serve as a layer of indirection between the specific
 * malloc implementation used, and actual calls to malloc() and
 * free().
 *
 * TODO: Move this functionality into libemhfc once it exists, and
 * name it consistently with libc, i.e., malloc.[ch].
 */
#include <tlsf.h>
#include <scode.h> /* only for perf ctr stuff */
#include <malloc.h>

#include <tv_log.h>

tlsf_pool g_pool;
void mem_init(void){
    static uint8_t memory_pool[HEAPMEM_POOLSIZE];
    g_pool = tlsf_create(memory_pool, HEAPMEM_POOLSIZE);
}

/* size_t heapmem_get_used_size(void) */
/* { */
/*   return get_used_size(memory_pool); */
/* } */

void *malloc(size_t size)
{
  void *p;
  perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_SAFEMALLOC], 0/*FIXME*/);

  EU_CHK_W( p = tlsf_malloc(g_pool, size),
            eu_warn_e( "malloc: allocation of size %d failed.", size));

 out:
  perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_SAFEMALLOC], 0/*FIXME*/);
  return p;
}

void *calloc(size_t nmemb, size_t size)
{
  void *p;
  p = tlsf_malloc(g_pool, nmemb * size);

  if(NULL != p) {
    memset(p, 0, nmemb * size);
  }

  return p;
}

void *realloc(void *ptr, size_t size)
{
  return tlsf_realloc(g_pool, ptr, size);
}

void free(void *ptr)
{
  tlsf_free(g_pool, ptr);
}
