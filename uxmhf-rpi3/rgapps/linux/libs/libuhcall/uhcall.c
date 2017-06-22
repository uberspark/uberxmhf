/*
 * uhcall -- guest interface for micro hypervisor hypercall
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>

#include <uhcall.h>

//////
// va_to_pa: virtual to physical address mapping
// return true on success, false on error
//////
bool uhcall_va2pa(void *vaddr, uint64_t *paddr) {
	FILE *pagemap;
	uint32_t offset;
	uint64_t page_frame_number = 0;

	//sanity check incoming parameters
	if (paddr == NULL)
		return false;

	// open the pagemap file for the current process
	pagemap = fopen("/proc/self/pagemap", "rb");
	if(pagemap == NULL)
		return false;	//unable to open pagemap file

	// seek to the page that vaddr is on
   offset = (uint32_t)vaddr / getpagesize() * UHCALL_PM_LENGTH;
   if(fseek(pagemap, (uint32_t)offset, SEEK_SET) != 0)
      return false; //Failed to seek pagemap to proper location

   // The page frame number is in bits 0-54 so read the
   // first 7 bytes and clear the 55th bit
   fread(&page_frame_number, 1, UHCALL_PM_LENGTH-1, pagemap);

   page_frame_number &= 0x7FFFFFFFFFFFFF;

   fclose(pagemap);

   *paddr = (page_frame_number << UHCALL_PM_PAGE_SHIFT);
   return true;
}
