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

/* dev.c routines to handle all DEV functions for TrustVisor
 * Written for TrustVisor by Arvind Seshadri and Ning Qu
 */

#include <types.h>
#include <processor.h>
#include <error.h>
#include <visor.h>
#include <paging.h>
#include <heap.h>
#include <svm.h>
#include <print.h>
#include <string.h>
#include <prot.h>
#include <io.h>
#include <pci.h>
#include <dev.h>

u32 init_dev_capoff __attribute__ ((section ("_init_data")));
u32 dev_capoff;

void find_dev(void) __attribute__ ((section ("_init_text")));
void init_dev_boot(void) __attribute__ ((section ("_init_text")));
void init_dev_rt1(void) __attribute__ ((section ("_init_text")));
void init_dev_rt2(void) __attribute__ ((section ("_init_text")));
void remove_dev_boot(void) __attribute__ ((section ("_init_text")));

/* search for DEV function support in PCI configuration space */
void find_dev(void)
{
  pci_config_reg_addr_t config_reg;
  dev_hdr_t dev_hdr;
  u32 capoff;
  u32 tmp;

  config_reg.fields.offset = PCI_CONF_HDR_ID;
  config_reg.fields.function = DEV_FUNCTION;
  config_reg.fields.device = DEV_DEVICE;
  config_reg.fields.bus = DEV_BUS;
  config_reg.fields.resv = 0;
  config_reg.fields.enabled = 1;
  tmp = init_read_pci_config_dword(&config_reg);

  if ((tmp != DEV_PCI_DEVICE_ID) &&
      (tmp != DEV_PCI_DEVICE_ID_SAHARA))
    EARLY_FAIL();
  
  config_reg.fields.offset = PCI_CONF_HDR_CMD;
  tmp = init_read_pci_config_dword(&config_reg);
  if (!(tmp & 0x100000))
    EARLY_FAIL();
  
  config_reg.fields.offset = PCI_CONF_HDR_CAP;
  capoff = init_read_pci_config_dword(&config_reg) & 0xff;
  while (capoff)
  {
    config_reg.fields.offset = capoff;
    dev_hdr.bytes = init_read_pci_config_dword(&config_reg);
    if ((dev_hdr.fields.cap_id == CAP_ID) && 
        (dev_hdr.fields.cap_type == DEV_CAP_BITS))
      break; 
    else
    {
      config_reg.fields.offset = capoff + PCI_CAP_OFFSET;
      capoff = init_read_pci_config_dword(&config_reg) & 0xff;
    }
  }
 
  if (capoff)
    init_dev_capoff = capoff;
  else
    EARLY_FAIL();
}

/* initialize DEV protection for bootstrap code of TrustVisor before relocation */
void init_dev_boot(void)
{
  
  dev_cap_t dev_cap;
  dev_map_t dev_map;
  dev_base_low_t dev_base_low;
  dev_base_hi_t dev_base_hi;
  dev_cr_t dev_cr;
  u32 i;

  /* Read the DEV revision, and the number of maps and domains supported */
  dev_cap.bytes = read_dev_fn(DEV_CAP, 0);

  /* Disable all the DEV_MAPs just to be safe. SVM manual does not say what 
   * the reset state of the DEV_MAP registers is.
   */
  dev_map.fields.v0 = 0;
  dev_map.fields.v1 = 0;
  for (i = 0; i < dev_cap.fields.n_maps; i ++)
    init_write_dev_fn(DEV_MAP, i, dev_map.bytes);

  /* Set up an initial DEV to cover first 64 MB of RAM. Allocate the
   * DEV to domain 0 since that is the domain a device is allocated to
   * when there no entries for the device in the DEV_MAP registers.
   * note: before verified, we avoid to use runtime code, such as memset 
   */
  init_memset(init_dev_bit_vector, (u32)0xffffffff, 
	 (u32)((VISOR_LOAD_START + VISOR_INIT_SIZE + VISOR_RUNTIME_SIZE) 
	       >> LG_BASE2_BYTES_PER_DEV_BIT)/8);

  /* Set the DEV_BASE_HIGH and DEV_BASE_LOW registers of domain 0 */
  dev_base_hi.bytes = 0; /* ASSUMPTION: Init DEV vector lies within 4GB */ 
  init_write_dev_fn(DEV_BASE_HI, 0, dev_base_hi.bytes);
  dev_base_low.fields.valid = 1;
  dev_base_low.fields.protect = 0;
  dev_base_low.fields.size = 0;
  dev_base_low.fields.resv = 0;
  dev_base_low.fields.base_addr = (u32)init_dev_bit_vector >> 12;
  init_write_dev_fn(DEV_BASE_LO, 0, dev_base_low.bytes);

  /* Invalidate the DEV_BASE_HIGH and DEV_BASE_LOW registers of all other
   * domains.
   */
  dev_base_low.fields.valid = 0;
  dev_base_low.fields.base_addr = 0;
  for (i = 1; i < dev_cap.fields.n_dom; i ++){
    init_write_dev_fn(DEV_BASE_HI, i, dev_base_hi.bytes);
    init_write_dev_fn(DEV_BASE_LO, i, dev_base_low.bytes);
  }

  /* Set the DEV_CR register to enable DEV protections */
  dev_cr.fields.enable = 1;
  dev_cr.fields.mem_clr = 0;
  dev_cr.fields.iospen = 1;
  dev_cr.fields.mce_en = 0;
  dev_cr.fields.invl = 0;
  /* Clearing the protection set by skinit should not be a problem
   * since we are simultaneously setting DEV protections over the
   * first 64 MB of RAM.
   */
  dev_cr.fields.sl_dev_en = 0; 
  dev_cr.fields.walk_probe = 0;
  dev_cr.fields.resv = 0;
  init_write_dev_fn(DEV_CR, 0, dev_cr.bytes);
}

/* switch to runtime DEV bit vector before relocation */
void init_dev_rt1(void)
{
  dev_base_hi_t dev_base_hi;
  dev_base_low_t dev_base_low;
  /* Setup the runtime DEV vector to protect the memory region to
   * which TrustVisor's runtime will be relocated as well as the memory 
   * currently occupied by the initialization code and the runtime.
   */
  dev_capoff = init_dev_capoff;
  set_dev_prot(visor_relocate_address, VISOR_RUNTIME_SIZE);
  set_dev_prot(VISOR_LOAD_START, VISOR_INIT_SIZE + VISOR_RUNTIME_SIZE);
  /* Set the DEV_BASE_HIGH and DEV_BASE_LOW registers of domain 0 */
  dev_base_hi.bytes = 0; /* ASSUMPTION: Init DEV vector lies within 4GB */ 
  write_dev_fn(DEV_BASE_HI, 0, dev_base_hi.bytes);
  dev_base_low.fields.valid = 1;
  dev_base_low.fields.protect = 0;
  dev_base_low.fields.size = 0;
  dev_base_low.fields.resv = 0;
 
  /* Switch to the DEV vector in the relocated runtime */
  dev_base_low.fields.base_addr = (u32)dev_bit_vector >> 12;
  write_dev_fn(DEV_BASE_LO, 0, dev_base_low.bytes);
  dev_cache_invalidate();
}

/* switch to runtime DEV bit vector after relocation */
void init_dev_rt2(void)
{
  dev_base_low_t dev_base_low;
  /* Setup the runtime DEV vector to protect the memory region to
   * which TrustVisor's runtime will be relocated as well as the memory 
   * occupied by the initialization code.
   */
  dev_base_low.bytes = read_dev_fn(DEV_BASE_LO, 0);
  /* Switch to the DEV vector in the relocated runtime */
  dev_base_low.fields.base_addr = (u32)__pa((u32)dev_bit_vector) >> 12;
  write_dev_fn(DEV_BASE_LO, 0, dev_base_low.bytes);
  dev_cache_invalidate();
  printf("INFO: Switch to runtime DEV protection vector\n");
}

/* remove DEV protection for initialization code and original runtime code */
void remove_dev_boot(void)
{
  /* Setup the runtime DEV vector to protect the memory region to
   * which TrustVisor's runtime will be relocated as well as the memory 
   * occupied by the initialization code.
   */
  clear_dev_prot(VISOR_LOAD_START, VISOR_INIT_SIZE + VISOR_RUNTIME_SIZE);
  DEBUG printf("DEBUG: Remove DEV protection for init section of TrustVisor\n");
}
