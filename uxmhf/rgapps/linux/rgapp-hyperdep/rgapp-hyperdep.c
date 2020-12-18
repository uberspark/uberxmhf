/*
 * XMHF rich guest app for hyperdep hypapp
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <stdio.h>
#include <sys/mman.h>
#include <errno.h>

typedef unsigned char uint8_t;
typedef unsigned int uint32_t;
typedef unsigned long long int uint64_t;


#define PAGE_SHIFT 12
#define PAGEMAP_LENGTH 8


//////
// hyperdep test harness

//////////////////////////////////////////////////////////////////////////////
// xhhyperdep test

__attribute__((aligned(4096))) static uint8_t testxhhyperdep_page[4096];

#define HYPERDEP_ACTIVATEDEP			0xC0
#define HYPERDEP_DEACTIVATEDEP			0xC1

typedef void (*DEPFN)(void);

static void __vmcall(uint32_t eax, uint32_t ebx, uint32_t edx){
	asm volatile (
			"movl %0, %%eax \r\n"
			"movl %1, %%ebx \r\n"
			"movl %2, %%edx \r\n"
			"vmcall \r\n"
			: /*no output*/
			: "g" (eax), "g" (ebx), "g" (edx)
			: "%eax", "%ebx", "%edx"
	);
}


static uint64_t va_to_pa(void *vaddr) {
	FILE *pagemap;
	unsigned long offset;
	uint64_t page_frame_number = 0;

	// open the pagemap file for the current process
	pagemap = fopen("/proc/self/pagemap", "rb");
	if(pagemap == NULL){
		printf("\n%s: unable to open pagemap file. exiting!", __FUNCTION__);
		exit(1);
	}

	// seek to the page that vaddr is on
   offset = (unsigned long)vaddr / getpagesize() * PAGEMAP_LENGTH;
   if(fseek(pagemap, (unsigned long)offset, SEEK_SET) != 0) {
      printf("\n%s: Failed to seek pagemap to proper location", __FUNCTION__);
      exit(1);
   }

   // The page frame number is in bits 0-54 so read the first 7 bytes and clear the 55th bit
   fread(&page_frame_number, 1, PAGEMAP_LENGTH-1, pagemap);

   page_frame_number &= 0x7FFFFFFFFFFFFF;

   fclose(pagemap);

   return (page_frame_number << PAGE_SHIFT);
}



void do_testxhhyperdep(uint32_t gpa){
    DEPFN fn = (DEPFN)&testxhhyperdep_page;
    uint32_t i;

    testxhhyperdep_page[0] = 0xC3; //ret instruction

    printf("\n%s: Going to activate DEP on page %x", __FUNCTION__, gpa);

    __vmcall(HYPERDEP_ACTIVATEDEP,  0, gpa);

    printf("\n%s: Activated DEP", __FUNCTION__);

    /*//////
    //test attack
    //////
    {
	    printf("\n%s: Proceeding with DEP attack...\n", __FUNCTION__);
    	if(mprotect(&testxhhyperdep_page, sizeof(testxhhyperdep_page), (PROT_READ | PROT_WRITE | PROT_EXEC)) != 0){
    	    printf("\n%s: Could not change page protections: %s\n", __FUNCTION__, strerror(errno));
    	    exit(1);
    	}
	    fn();
    	printf("\n%s: DEP attack worked\n", __FUNCTION__);
    }*/

    //write some stuff to the data page
    printf("\n%s: Writing data to buffer...", __FUNCTION__);
    for(i=0; i < 255; i++)
    	testxhhyperdep_page[i]=(uint8_t)i;
    printf("\n%s: data written successfully", __FUNCTION__);


    printf("\n%s: Going to de-activate DEP on page %x", __FUNCTION__, gpa);

    __vmcall(HYPERDEP_DEACTIVATEDEP,  0, gpa);

    printf("\n%s: Deactivated DEP", __FUNCTION__);

}



void main(void){
    printf("\n%s: DEP buffer at 0x%08x", __FUNCTION__, &testxhhyperdep_page);

    printf("\n%s: proceeding to lock DEP page...", __FUNCTION__);

    //lock the DEP page in memory so we have it pinned down
	if(mlock(&testxhhyperdep_page, sizeof(testxhhyperdep_page)) == -1) {
		  printf("\nFailed to lock page in memory: %s\n", strerror(errno));
		  exit(1);
	}

    printf("\n%s: DEP page locked", __FUNCTION__);

    printf("\n%s: DEP buffer at paddr=%08x", __FUNCTION__, va_to_pa(&testxhhyperdep_page));



	do_testxhhyperdep(va_to_pa(&testxhhyperdep_page));

    printf("\n%s: proceeding to unlock DEP page...", __FUNCTION__);

    //unlock the DEP page
	if(munlock(&testxhhyperdep_page, sizeof(testxhhyperdep_page)) == -1) {
		  printf("\nFailed to unlock page in memory: %s\n", strerror(errno));
		  exit(1);
	}

    printf("\n%s: DEP page unlocked", __FUNCTION__);


    printf("\n\n");
}
