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

/**
 * heap.[ch] serve as a layer of indirection between the specific
 * malloc implementation used, and actual calls to malloc() and
 * free().
 *
 * TODO: Move this functionality into libemhfc once it exists, and
 * name it consistently with libc, i.e., malloc.[ch].
 */
#include <tlsf.h>
#include <scode.h> /* only for perf ctr stuff */
#include <malloc.h>

static u8 memory_pool[HEAPMEM_POOLSIZE];
void mem_init(void){
  init_memory_pool(HEAPMEM_POOLSIZE, memory_pool);
}

size_t heapmem_get_used_size(void)
{
  return get_used_size(memory_pool);
}

void *malloc(size_t size)
{
	void *p;
    perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_SAFEMALLOC], 0/*FIXME*/);

    p = tlsf_malloc(size);

    perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_SAFEMALLOC], 0/*FIXME*/);
    
	if (!p) {
        dprintf(LOG_ERROR, "malloc: allocation of size %d failed.", size);
	}

	return p;
}

void free(void *ptr)
{
	if (ptr) {
		tlsf_free(ptr);
	}
}


