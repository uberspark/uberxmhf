/*
 * XMHF rich guest app for aprvexec hypapp
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
// aprvexec test harness
//////


extern void do_testxhapprovexec_functoprotect(void);



#define APRVEXEC_LOCK     			0xD0
#define APRVEXEC_UNLOCK   			0xD1

void do_testxhapprovexec(void){
    uint32_t fva = &do_testxhapprovexec_functoprotect;
	uint32_t fpa;

    printf("\n%s: Target function virtual-address=0x%08x\n", __FUNCTION__, fva);

    printf("\n%s: Proceeding to lock function in memory...", __FUNCTION__);

    if(mlock(fva, 4096) == -1) {
    	  printf("\nFailed to lock page in memory: %s\n", strerror(errno));
    	  exit(1);
    }
    if(mprotect(fva, 4096, (PROT_READ | PROT_WRITE | PROT_EXEC)) != 0){
        printf("\n%s: Could not change page protections: %s\n", __FUNCTION__, strerror(errno));
        exit(1);
    }

    printf("\n%s: Locked function in memory", __FUNCTION__);

    fpa=	va_to_pa(&do_testxhapprovexec_functoprotect);

    printf("\n%s: Target function physical-address=0x%08x\n", __FUNCTION__, fpa);


    printf("\n%s: proceeding to approve function...", __FUNCTION__);

    __vmcall(APRVEXEC_LOCK, 0, fpa);

    printf("\n%s: Approved function\n", __FUNCTION__);

    printf("\n%s: Calling function..\n", __FUNCTION__);
    do_testxhapprovexec_functoprotect();
    printf("\n%s: returned back\n", __FUNCTION__);

    //////
    //code modification test attack
    //////
    //printf("\n%s: Preparing to execute code modification attack...\n", __FUNCTION__);
    //
    //{
    //	*((uint8_t *)&do_testxhapprovexec_functoprotect) = 0xAB;
    //}
    //printf("\n%s: Code modification attack successful\n", __FUNCTION__);

    //////



    printf("\n%s: Going to release approved execution at fn va=%08x, pa=%08x\n", __FUNCTION__, fva, fpa);

    __vmcall(APRVEXEC_UNLOCK, 0, fpa );

    printf("\n%s: Released approved execution", __FUNCTION__);

    printf("\n%s: Proceeding to unlock function in memory...", __FUNCTION__);

    if(munlock(fva, 4096) == -1) {
    	  printf("\nFailed to unlock page in memory: %s\n", strerror(errno));
    	  exit(1);
    }

    printf("\n%s: unlocked function in memory", __FUNCTION__);


}





void main(void){
    printf("\n%s: Proceeding with aprvexec test...", __FUNCTION__);

    do_testxhapprovexec();

    printf("\n%s: aprvexec test done", __FUNCTION__);
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

