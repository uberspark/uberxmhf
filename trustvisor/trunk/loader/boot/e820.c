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

/* e820.c Sanitize and copy BIOS e820 map 
 * Adapted from Xen for TrustVisor by Arvind Seshadri 
 */

#include <types.h>
#include <multiboot.h>
#include <e820.h>
#include <print.h>
#include <string.h>
#include <error.h>
#include <visor.h>
#include <paging.h>
#include <svm.h>

unsigned long long opt_mem __attribute__ ((section ("_init_data")));
struct e820map e820 __attribute__ ((section ("_init_data")));
struct change_member {
    struct e820entry *pbios; /* pointer to original bios entry */
    unsigned long long addr; /* address for this change point */
};
static struct change_member change_point_list[2*E820MAX] \
__attribute__ ((section ("_init_data")));
static struct change_member *change_point[2*E820MAX] \
__attribute__ ((section ("_init_data")));
static struct e820entry *overlap_list[E820MAX] \
__attribute__ ((section ("_init_data")));
static struct e820entry new_bios[E820MAX] \
__attribute__ ((section ("_init_data")));
static struct e820entry e820_raw[E820MAX] \
__attribute__ ((section ("_init_data"))); 

static void add_memory_region(unsigned long long start,
                                     unsigned long long size, u32 type) \
  __attribute__ ((section ("_init_text")));
static void print_e820_memory_map(struct e820entry *map, u32 entries) \
  __attribute__ ((section ("_init_text")));
static int sanitize_e820_map(struct e820entry *biosmap, u32 *pnr_map) \
  __attribute__ ((section ("_init_text")));
static void copy_e820_map(struct e820entry *biosmap, u32 *n_map) \
  __attribute__ ((section ("_init_text")));
static void machine_specific_memory_setup(struct e820entry *raw, u32 *raw_nr) \
  __attribute__ ((section ("_init_text")));
static u32 find_max_pfn(void) __attribute__ ((section ("_init_text")));
static u32 init_e820(struct e820entry *raw, u32 *raw_nr)
  __attribute__ ((section ("_init_text")));
u32 fix_e820(multiboot_info_t *) __attribute__ ((section ("_init_text")));

static void add_memory_region(unsigned long long start,
                                     unsigned long long size, u32 type)
{
  u32 x;
  x = e820.nr_map;
  
  if (x == E820MAX) {
    EARLY_FAIL();
  }

  e820.map[x].addr = start;
  e820.map[x].size = size;
  e820.map[x].type = type;
  e820.nr_map ++;
} /* add_memory_region */

static void print_e820_memory_map(struct e820entry *map, u32 entries)
{
  u32 i;
  
  for (i = 0; i < entries; i++) {
    switch (map[i].type) {
    case E820_RAM:	
      break;
    case E820_RESERVED:
      break;
    case E820_ACPI:
      break;
    case E820_NVS:
      break;
    default:	
      break;
    }
  }
}

/*
 * Sanitize the BIOS e820 map.
 *
 * Some e820 responses include overlapping entries.  The following 
 * replaces the original e820 map with a new one, removing overlaps.
 *
 */

static int sanitize_e820_map(struct e820entry *biosmap, u32 *pnr_map)
{
  struct change_member *change_tmp;
  unsigned long current_type, last_type;
  unsigned long long last_addr;
  u32 chgidx, still_changing;
  u32 overlap_entries;
  u32 new_bios_entry;
  u32 old_nr, new_nr, chg_nr;
  u32 i;
  
  /*
    Visually we're performing the following (1,2,3,4 = memory types)...
    
    Sample memory map (w/overlaps):
    ____22__________________
    ______________________4_
    ____1111________________
    _44_____________________
    11111111________________
    ____________________33__
    ___________44___________
    __________33333_________
    ______________22________
    ___________________2222_
    _________111111111______
    _____________________11_
    _________________4______
    
    Sanitized equivalent (no overlap):
    1_______________________
    _44_____________________
    ___1____________________
    ____22__________________
    ______11________________
    _________1______________
    __________3_____________
    ___________44___________
    _____________33_________
    _______________2________
    ________________1_______
    _________________4______
    ___________________2____
    ____________________33__
    ______________________4_
  */

  /* if there's only one memory region, don't bother */
  if (*pnr_map < 2)
    return -1;
  
  old_nr = *pnr_map;
  
  /* bail out if we find any unreasonable addresses in bios map */
  for (i=0; i<old_nr; i++)
    if (biosmap[i].addr + biosmap[i].size < biosmap[i].addr)
      return -1;
  
  /* create pointers for initial change-point information (for sorting) */
  for (i=0; i < 2*old_nr; i++)
    change_point[i] = &change_point_list[i];

  /* record all known change-points (starting and ending addresses),
     omitting those that are for empty memory regions */
  chgidx = 0;
  for (i=0; i < old_nr; i++)	{
    if (biosmap[i].size != 0) {
      change_point[chgidx]->addr = biosmap[i].addr;
      change_point[chgidx++]->pbios = &biosmap[i];
      change_point[chgidx]->addr = biosmap[i].addr + biosmap[i].size;
      change_point[chgidx++]->pbios = &biosmap[i];
    }
  }
  chg_nr = chgidx;    	/* true number of change-points */
    
  /* sort change-point list by memory addresses (low -> high) */
  still_changing = 1;
  while (still_changing)	{
    still_changing = 0;
        for (i=1; i < chg_nr; i++)  {
	  /* if <current_addr> > <last_addr>, swap */
	  /* or, if current=<start_addr> & last=<end_addr>, swap */
	  if ((change_point[i]->addr < change_point[i-1]->addr) ||
	      ((change_point[i]->addr == change_point[i-1]->addr) &&
	       (change_point[i]->addr == change_point[i]->pbios->addr) &&
	       (change_point[i-1]->addr != change_point[i-1]->pbios->addr))
	      )
            {
	      change_tmp = change_point[i];
	      change_point[i] = change_point[i-1];
	      change_point[i-1] = change_tmp;
	      still_changing=1;
            }
        }
  }
  
  /* create a new bios memory map, removing overlaps */
  overlap_entries=0;	 /* number of entries in the overlap table */
  new_bios_entry=0;	 /* index for creating new bios map entries */
  last_type = 0;		 /* start with undefined memory type */
  last_addr = 0;		 /* start with 0 as last starting address */
  /* loop through change-points, determining affect on the new bios map */
  for (chgidx=0; chgidx < chg_nr; chgidx++)
    {
      /* keep track of all overlapping bios entries */
      if (change_point[chgidx]->addr == change_point[chgidx]->pbios->addr)
        {
	  /* add map entry to overlap list (> 1 entry implies an overlap) */
	  overlap_list[overlap_entries++]=change_point[chgidx]->pbios;
        }
      else
        {
	  /* remove entry from list (order independent, so swap with last) */
	  for (i=0; i<overlap_entries; i++)
            {
	      if (overlap_list[i] == change_point[chgidx]->pbios)
		overlap_list[i] = overlap_list[overlap_entries-1];
            }
	  overlap_entries--;
        }
      /* if there are overlapping entries, decide which "type" to use */
      /* (larger value takes precedence -- 1=usable, 2,3,4,4+=unusable) */
      current_type = 0;
      for (i=0; i<overlap_entries; i++)
	if (overlap_list[i]->type > current_type)
	  current_type = overlap_list[i]->type;
      /* continue building up new bios map based on this information */
      if (current_type != last_type)	{
	if (last_type != 0)	 {
	  new_bios[new_bios_entry].size =
	    change_point[chgidx]->addr - last_addr;
	  /* move forward only if the new size was non-zero */
	  if (new_bios[new_bios_entry].size != 0)
	    if (++new_bios_entry >= E820MAX)
	      break; 	/* no more space left for new bios entries */
	}
	if (current_type != 0)	{
	  new_bios[new_bios_entry].addr = change_point[chgidx]->addr;
	  new_bios[new_bios_entry].type = current_type;
	  last_addr=change_point[chgidx]->addr;
	}
	last_type = current_type;
      }
    }
  new_nr = new_bios_entry;   /* retain count for new bios entries */
  
  /* copy new bios mapping into original location */
  memcpy(biosmap, new_bios, new_nr*sizeof(struct e820entry));
  *pnr_map = new_nr;
  
  return 0;
}

/*
 * Copy the BIOS e820 map into a safe place.
 *
 * Sanity-check it while we're at it..
 *
 * If we're lucky and live on a modern system, the setup code
 * will have given us a memory map that we can use to properly
 * set up memory.  If we aren't, we'll fake a memory map.
 *
 * We check to see that the memory map contains at least 2 elements
 * before we'll use it, because the detection code in setup.S may
 * not be perfect and most every PC known to man has two memory
 * regions: one from 0 to 640k, and one from 1mb up.  (The IBM
 * thinkpad 560x, for example, does not cooperate with the memory
 * detection code.)
 */
static void copy_e820_map(struct e820entry *biosmap, u32 *n_map)
{
  u32 nr_map = *n_map;
  
  /* Only one memory region (or negative)? Ignore it */
  if (nr_map < 2)
    return;
  
  do {
    unsigned long long start = biosmap->addr;
    unsigned long long size = biosmap->size;
    unsigned long long end = start + size;
    unsigned long type = biosmap->type;
    
    /* Overflow in 64 bits? Ignore the memory map. */
    if (start > end)
      return; 
    /*
     * Some BIOSes claim RAM in the 640k - 1M region.
     * Not right. Fix it up.
     */
    if (type == E820_RAM) {
      if (start < 0x100000ULL && end > 0xA0000ULL) {
	if (start < 0xA0000ULL)
	  add_memory_region(start, 0xA0000ULL-start, type);
	if (end <= 0x100000ULL)
	  continue;
	start = 0x100000ULL;
	size = end - start;
      }
    }
    add_memory_region(start, size, type);
  } while (biosmap++,--nr_map);
  return;
}

static void machine_specific_memory_setup(struct e820entry *raw, u32 *raw_nr)
{
  sanitize_e820_map(raw, raw_nr);
  copy_e820_map(raw, raw_nr);
  return;
}

/*
 * Find the highest page frame number we have available
 */
static u32 find_max_pfn(void)
{
  u32 i, max_pfn = 0;

  for (i = 0; i < e820.nr_map; i++) {
    unsigned long start, end;
    /* RAM? */
    if (e820.map[i].type != E820_RAM)
      continue;
    start = ((e820.map[i].addr) + PAGE_SIZE_4K - 1) >> PAGE_SHIFT_4K;
    end = (e820.map[i].addr + e820.map[i].size) >> PAGE_SHIFT_4K;
    if (start >= end)
      continue;
    if (end > max_pfn)
      max_pfn = end;
  }

  return (max_pfn);
}

static u32 init_e820(struct e820entry *raw, u32 *raw_nr)
{
  machine_specific_memory_setup(raw, raw_nr);
  print_e820_memory_map(e820.map, e820.nr_map);
  return find_max_pfn();
}



u32 fix_e820(multiboot_info_t *mbi){
  u32 e820_raw_nr = 0, e820_warn = 0, bytes = 0;
  
  while ( bytes < mbi->mmap_length ){
    memory_map_t *map = (memory_map_t*)(mbi->mmap_addr + bytes);  
    /*
     * This is a gross workaround for a BIOS bug. Some bootloaders do
     * not write e820 map entries into pre-zeroed memory. This is
     * okay if the BIOS fills in all fields of the map entry, but
     * some broken BIOSes do not bother to write the high word of
     * the length field if the length is smaller than 4GB. We
     * detect and fix this by flagging sections below 4GB that
     * appear to be larger than 4GB in size.
     */
    if ( (map->base_addr_high == 0) && (map->length_high != 0) ){
      e820_warn = 1;
      map->length_high = 0;
    }
      
    e820_raw[e820_raw_nr].addr = 
      ((u64)map->base_addr_high << 32) | (u64)map->base_addr_low;
    e820_raw[e820_raw_nr].size = 
      ((u64)map->length_high << 32) | (u64)map->length_low;
    e820_raw[e820_raw_nr].type = 
      (map->type > E820_SHARED_PAGE) ? E820_RESERVED : map->type;
    e820_raw_nr++;
    bytes += map->size + 4;
  }

  return init_e820(e820_raw, &e820_raw_nr);
}
