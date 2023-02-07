/*
 * XMHF rich guest app for ssteptrace hypapp
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <stdio.h>
#include <sys/mman.h>
#include <errno.h>


//////////////////////////////////////////////////////////////////////////////
// base types

typedef unsigned char uint8_t;
typedef unsigned int uint32_t;
typedef unsigned long long int uint64_t;


#define PAGE_SHIFT 12
#define PAGEMAP_LENGTH 8


//////
// vmcall interface
//////
__attribute__ ((always_inline)) static inline void __vmcall(uint32_t eax, uint32_t ebx, uint32_t edx){
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


//////
// va_to_pa: virtual to physical address mapping
//////
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



//////
// ssteptrace test harness
//////

#define SSTEPTRACE_REGISTER    			0xE0
#define SSTEPTRACE_ON          			0xE1
#define SSTEPTRACE_OFF         			0xE2

__attribute__((aligned(4096))) void do_testssteptrace(void){
	uint32_t fva = &do_testssteptrace;
	uint32_t fpa;

	printf("\n%s: Proceeding to lock test function at va=0x%08x...", __FUNCTION__, fva);

	if(mlock(fva, 4096) == -1) {
		printf("\nFailed to lock page in memory: %s\n", strerror(errno));
		exit(1);
	}

	fpa = va_to_pa(fva);

	printf("\n%s: Locked test function at va=0x%08x ==> pa=0x%08x", __FUNCTION__, fva, fpa);

	printf("\n%s: Registering test function...", __FUNCTION__);
	__vmcall(SSTEPTRACE_REGISTER, 0, fpa);
	printf("\n%s: test function registered", __FUNCTION__);

	printf("\n%s: Turning on tracing...\n", __FUNCTION__);

	__vmcall(SSTEPTRACE_ON, 0, 0);

	__vmcall(SSTEPTRACE_OFF, 0 , 0);

	printf("\n%s: Tracing off\n", __FUNCTION__);

	asm volatile(
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        ".byte 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 \r\n"
	        :
	        :
	        :
	    );

	printf("\n%s: Proceeding to unlock test function at va=0x%08x...", __FUNCTION__, fva);

	if(munlock(fva, 4096) == -1) {
		  printf("\nFailed to unlock page in memory: %s\n", strerror(errno));
		  exit(1);
	}

	printf("\n%s: unlocked test function", __FUNCTION__);

}



void main(void){
    printf("\n%s: Proceeding with ssteptrace test...", __FUNCTION__);

    do_testssteptrace();

    printf("\n%s: ssteptrace test done", __FUNCTION__);
    printf("\n\n");
}

//////
// building pieces
//////

//__attribute__((aligned(4096))) static uint8_t testxhhyperdep_page[4096];


//printf("\n%s: DEP page unlocked", __FUNCTION__);

//if(munlock(&testxhhyperdep_page, sizeof(testxhhyperdep_page)) == -1) {
//	  printf("\nFailed to unlock page in memory: %s\n", strerror(errno));
//	  exit(1);
//}

//if(mlock(&testxhhyperdep_page, sizeof(testxhhyperdep_page)) == -1) {
//	  printf("\nFailed to lock page in memory: %s\n", strerror(errno));
//	  exit(1);
//}

//	if(mprotect(&testxhhyperdep_page, sizeof(testxhhyperdep_page), (PROT_READ | PROT_WRITE | PROT_EXEC)) != 0){
//	    printf("\n%s: Could not change page protections: %s\n", __FUNCTION__, strerror(errno));
//	    exit(1);
//	}

