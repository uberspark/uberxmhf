#ifndef INCLUDED_xmhf_tlsf
#define INCLUDED_xmhf_tlsf

/*
** Two Level Segregated Fit memory allocator, version 1.9.
** Written by Matthew Conte, and placed in the Public Domain.
**	http://xmhf_tlsf.baisoku.org
**
** Based on the original documentation by Miguel Masmano:
**	http://rtportal.upv.es/rtmalloc/allocators/xmhf_tlsf/index.shtml
**
** Please see the accompanying Readme.txt for implementation
** notes and caveats.
**
** This implementation was written to the specification
** of the document, therefore no GPL restrictions apply.
*/

#include <stdio.h>
#include <stddef.h>

#if defined(__cplusplus)
extern "C" {
#endif

/* Create/destroy a memory pool. */
typedef void* xmhf_tlsf_pool;
xmhf_tlsf_pool xmhf_tlsf_create(void* mem, size_t bytes);
void xmhf_tlsf_destroy(xmhf_tlsf_pool pool);

/* malloc/memalign/realloc/free replacements. */
void* xmhf_tlsf_malloc(xmhf_tlsf_pool pool, size_t bytes);
void* xmhf_tlsf_memalign(xmhf_tlsf_pool pool, size_t align, size_t bytes);
void* xmhf_tlsf_realloc(xmhf_tlsf_pool pool, void* ptr, size_t size);
void xmhf_tlsf_free(xmhf_tlsf_pool pool, void* ptr);

/* Debugging. */
typedef void (*xmhf_tlsf_walker)(void* ptr, size_t size, int used, void* user);
void xmhf_tlsf_walk_heap(xmhf_tlsf_pool pool, xmhf_tlsf_walker walker, void* user);
/* Returns nonzero if heap check fails. */
int xmhf_tlsf_check_heap(xmhf_tlsf_pool pool);

/* Returns internal block size, not original request size */
size_t xmhf_tlsf_block_size(void* ptr);

/* Overhead of per-pool internal structures. */
size_t xmhf_tlsf_overhead(void);

#if defined(__cplusplus)
};
#endif

#endif
