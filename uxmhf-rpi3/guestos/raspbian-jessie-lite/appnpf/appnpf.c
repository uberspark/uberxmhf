#include<stdio.h>
#include<stdlib.h>
#include<errno.h>
#include<fcntl.h>
#include<string.h>
#include<unistd.h>
#include <sys/mman.h>


//////////////////////////////////////////////////////////////////////////////
// base types

typedef unsigned char u8;
typedef unsigned int u32;
typedef unsigned long long int u64;


#define PAGE_SHIFT 12
#define PAGEMAP_LENGTH 8


__attribute__((aligned(4096))) static volatile u8 test_buffer[4096];
int fd;


//////
// va_to_pa: virtual to physical address mapping
//////
static u64 va_to_pa(void *vaddr) {
	FILE *pagemap;
	unsigned long offset;
	u64 page_frame_number = 0;

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



void appnpf_noaccess(u32 address){
	int ret;

	ret = write(fd, address, 2);
	if (ret < 0){
	  perror("Failed to issue hypercall.");
	  return errno;
	}
}


void appnpf_restoreaccess(u32 address){
	int ret;

	ret = write(fd, address, 3);
	if (ret < 0){
	  perror("Failed to issue hypercall.");
	  return errno;
	}
}



void do_testnpf(void){
    u32 va = (u32)&test_buffer;
    u32 pa;
    u32 val;

    printf("\n%s: Target buffer virtual-address=0x%08x\n", __FUNCTION__, va);

    printf("\n%s: Proceeding to lock buffer in memory...", __FUNCTION__);

    if(mlock(va, 4096) == -1) {
    	  printf("\nFailed to lock page in memory: %s\n", strerror(errno));
    	  exit(1);
    }
    if(mprotect(va, 4096, (PROT_READ | PROT_WRITE)) != 0){
        printf("\n%s: Could not change page protections: %s\n", __FUNCTION__, strerror(errno));
        exit(1);
    }

    printf("\n%s: Locked buffer in memory", __FUNCTION__);

    pa=	va_to_pa(&test_buffer);

    printf("\n%s: Target buffer physical-address=0x%08x\n", __FUNCTION__, pa);

    printf("\n%s: proceeding to set buffer to no-access", __FUNCTION__);

    appnpf_noaccess(pa);

    printf("\n%s: set buffer to no-access\n", __FUNCTION__);


    printf("\n%s: proceeding to write to buffer...\n", __FUNCTION__);

    test_buffer[5]='A';
    val = test_buffer[5];

    printf("\n%s: proceeding to set restore buffer protections", __FUNCTION__);

    appnpf_restoreaccess(pa);

    printf("\n%s: restored buffer protections\n", __FUNCTION__);

    printf("\n%s: val=0x%02x\n", __FUNCTION__, val);
}





void main(void){

	printf("\n%s: Proceeding with appnpf test...", __FUNCTION__);

	fd = open("/dev/hypcallchar", O_RDWR);             // Open the device with read/write access
	if (fd < 0){
	  perror("Failed to open the device...");
	  return errno;
	}

    do_testnpf();


    close(fd);

    printf("\n%s: appnpf test done", __FUNCTION__);
    printf("\n\n");
}

//////
// building pieces
//////

//__attribute__((aligned(4096))) static u8 testxhhyperdep_page[4096];


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

