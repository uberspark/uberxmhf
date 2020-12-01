/*
 * XMHF rich guest app for uhcalltest hypapp
 * author: amit vasudevan (amitvasudevan@acm.org)
 * author: matt mccormack (matthew.mccormack@live.com)
 */

#include <stdio.h>
#include <sys/mman.h>
#include <errno.h>
#include <elf.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <unistd.h>
#include <stdbool.h>

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
// uhcall
//////
bool uhcall(uint32_t uhcall_function, void *uhcall_buffer, uint32_t uhcall_buffer_len){
  uint64_t uhcall_buffer_paddr;
  if(uhcall_buffer==NULL && uhcall_buffer_len!=0){
    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
    return false;
  }
  if(uhcall_buffer!=NULL){
    if((((uint32_t)uhcall_buffer % 4096) + uhcall_buffer_len)>4096){
      printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
      return false;
    }
  }
  uhcall_buffer_paddr=va_to_pa(uhcall_buffer);
  if(mlock(uhcall_buffer, uhcall_buffer_len)==-1){
    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
    return false;
  }
  __vmcall(uhcall_function, 0, uhcall_buffer_paddr);
  if(munlock(uhcall_buffer, uhcall_buffer_len)==-1){
    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
    return false;
  }
  return true;
}
 

//////
// uhcalltest test harness
//////
#define UAPP_UHCALLTEST_FUNCTION_TEST   0x22

typedef struct{
  uint8_t in[16];
  uint8_t out[16];
}uhcalltest_param_t;

__attribute__ ((aligned(4096))) __attribute__((section(".data"))) uhcalltest_param_t uhctp;

void do_uhcalltest(void *bufptr){
  uhcalltest_param_t *ptr_uhctp = (uhcalltest_param_t *)bufptr;
  uint32_t i;
  uint8_t ch='a';

  printf("%s: start\n", __FUNCTION__);
  printf("%s: populating in[] and out[]...\n", __FUNCTION__);
  for(i=0;i<16;i++)
    ptr_uhctp->in[i] = ch+i;
  memset(&ptr_uhctp->out, 0, 16);
  printf("dumping in[]...\n");
  for(i=0;i<16;i++)
    printf("%c", ptr_uhctp->in[i]);
  printf("\n");
  //make hypcall
  if(!uhcall(UAPP_UHCALLTEST_FUNCTION_TEST, ptr_uhctp, sizeof(uhcalltest_param_t)))
    printf("hypercall FAILED\n");
  else
    printf("hypercall SUCCESS\n");
  printf("dumping out[]...\n");
  for(i=0;i<16;i++)
    printf("%c", ptr_uhctp->out[i]);
  printf("\n");
  printf("%s: end\n", __FUNCTION__);
}



__attribute__ ((aligned(4096))) int main(){
  uhcalltest_param_t *ptr_uhctp;
  printf("starting uhcalltest (with static buffer)...\n");
  do_uhcalltest((void *)&uhctp);
  printf("end uhcalltest (with static buffer)...\n");
  printf("starting uhcalltest (with dynamic buffer)...\n");
  if(posix_memalign(&ptr_uhctp, 4096, sizeof(uhcalltest_param_t))!=0){
    printf("%s: error: \n", __FUNCTION__);
    exit(1);
  }
  do_uhcalltest((void *)ptr_uhctp);
  free(ptr_uhctp);
  printf("end uhcalltest (with dynamic buffer)...\n");
  return 0;
}
