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

/*
 * Platform-independent routines shared between all PuTTY programs.
 */

#include <puttymem.h>
#include <tlsf.h>
#include <scode.h> /* perf ctr stuff */

/* ----------------------------------------------------------------------
 * My own versions of malloc, realloc and free. Because I want
 * malloc and realloc to bomb out and exit the program if they run
 * out of memory, realloc to reliably call malloc if passed a NULL
 * pointer, and free to reliably do nothing if passed a NULL
 * pointer. We can also put trace printouts in, if we need to; and
 * we can also replace the allocator with an ElectricFence-like
 * one.
 */

/* int totalmem = 0; */
static u8 memory_pool[PUTTYMEM_POOLSIZE];
void mem_init(void){
  init_memory_pool(PUTTYMEM_POOLSIZE, memory_pool);
}

size_t puttymem_get_used_size(void)
{
  return get_used_size(memory_pool);
}

void *safemalloc(size_t n, size_t size)
{
	void *p;
        perf_ctr_timer_start(&g_tv_perf_ctrs[TV_PERF_CTR_SAFEMALLOC], 0/*FIXME*/);

  //  struct st_timer_vars tv;
    //start_timer(&tv);

		 /*totalmem += size;
		 printf("Allocated %d bytes so far\n", totalmem);*/
	if (n > INT_MAX / size) {
		p = NULL;
	} else {
		size *= n;
		p = tlsf_malloc(size);
	}

   // stop_timer(&tv);
   // update_sum(&perf.sum_rsag_malloc, &tv);

        perf_ctr_timer_record(&g_tv_perf_ctrs[TV_PERF_CTR_SAFEMALLOC], 0/*FIXME*/);
    
	if (!p) {
	  dprintf(LOG_ERROR, "safemalloc: allocation of size %d failed.", size);
	  return NULL;
	}
	return p;
}

void safefree(void *ptr)
{
	if (ptr) {
		tlsf_free(ptr);
	}
}


