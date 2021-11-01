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

#ifndef TZDEV_TRUSTVISOR_H
#define TZDEV_TRUSTVISOR_H

#include "svcapi.h"
#include "tz.h"

#include <stdint.h>
#include <stddef.h>

#include <trustvisor/trustvisor.h>

/* FIXME: copied from paging.h in trustvisor. should use that directly */
#define PAGE_SIZE 0x1000
#define PAGE_SIZE_4K (1UL << 12)
#define PAGE_ALIGN_UP4K(size)   (((size) + PAGE_SIZE_4K - 1) & ~(PAGE_SIZE_4K - 1))
#define PAGE_ALIGN_4K(size)     ((size) & ~(PAGE_SIZE_4K - 1))

#define PAGE_ALIGNED_4K(size) (PAGE_ALIGN_4K(size) == size)

typedef void (*pal_fn_t)(uint32_t uiCommand, struct tzi_encode_buffer_t *psInBuf, struct tzi_encode_buffer_t *psOutBuf, tz_return_t *puiRv);

typedef struct {
  struct tv_pal_sections *sPageInfo;
  struct tv_pal_params *sParams;
  pal_fn_t pEntry;
} tv_service_t;

typedef struct {
  bool userspace_only;
} tv_device_open_options_t;

/* read (and optionally write) to the memory pages in the specified
 * range. use this to make sure pages are present for trustvisor
 * (e.g., for pointer parameters before calling a pal function)
 */
/* int scode_touch_range(void *ptr, size_t len, int do_write); */

/* convenience function for getting size of a section from end and start symbols */
size_t tv_ptr_diff(void *end, void *start);

/* initialize a tv_pal_sections struct, allocating page-aligned memory
 * for the parameters and stack.
 */
void tv_pal_sections_init(struct tv_pal_sections *scode_info,
                          size_t param_sz,
                          size_t stack_sz);

/* add a section to an scode_sections_info struct.
 * The struct should have already been initialized.
 */
void tv_pal_sections_add(struct tv_pal_sections *scode_info,
                         int type,
                         void *start_addr, size_t len);

/* Print tv_pal_sections_info to stdout */
void tv_pal_sections_print(struct tv_pal_sections *scode_info);

/* Register a PAL.
 * pageinfo describes the memory areas to be used by the PAL.
 *   These memory areas must be page-aligned (e.g., 4K-aligned).
 *   These areas must not be swapped out (use tv_lock_pal_sections)
 * params describes the parameters to the PAL function.
 * entry is a pointer to the PAL function.
 *
 * Once a function is registered, any call to that function
 * will take place in the secure environment.
 *
 * Returns 0 on success, nonzero on failure.
 */
int tv_pal_register(const struct tv_pal_sections *pageinfo,
                    const struct tv_pal_params *params,
                    const void *entry);

/* Unregister a PAL.
 * entry is a pointer to a function previously registered
 *   with tv_pal_register
 *
 * After unregistration, calls to the given function
 * no longer take place in the secure environment.
 *
 * Returns 0 on success, nonzero on failure.
 */
int tv_pal_unregister(void *entry);

/* share memory ranges with a PAL.
   The memory areas must be page-aligned, and must not be swapped out.
   (use tv_lock_range and\or tv_touch_range)
*/
int tv_pal_share(const void *entry, void **start, size_t *len, size_t count);

/* Test for presence of TrustVisor.
 *
 * Returns 0 on success, nonzero on failure.
 */
int tv_test(void);

/** 
 * Convenience function to load the linked PAL using the TZ
 * interfaces, and initialize the tzDevice, tzPalSession, and tzSvcId.
 */
tz_return_t tv_tz_init(tz_device_t*  tzDevice,
                       tz_session_t* tzPalSession,
                       tz_uuid_t*    tzSvcId,
                       pal_fn_t      pal_entry,
                       size_t        param_sz,
                       size_t        stack_sz);

/** 
 * Convenience function to gracefully unload the linked PAL using the
 * TZ interfaces, and tear down the tzPalSession and tzDevice.
 */
tz_return_t tv_tz_teardown(tz_device_t*  tzDevice,
                           tz_session_t* tzPalSession,
                           tz_uuid_t*    tzSvcId);


/* utility functions for locking ranges into memory. useful to call
   before and after registration, and before and after sharing
   memory */
int tv_lock_range(void *ptr, size_t len);
int tv_touch_range(void *ptr, size_t len, int do_write);
void tv_lock_pal_sections(const struct tv_pal_sections *scode_info);

int tv_unlock_range(void *ptr, size_t len);
void tv_unlock_pal_sections(const struct tv_pal_sections *scode_info);

#endif
