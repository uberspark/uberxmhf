/*
 * hypercall test program (uhcalltest)
 * author: amit vasudevan (amitvasudevan@acm.org)
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>

#include <uhcall.h>
#include <uhcalltest.h>

__attribute__((aligned(4096))) __attribute__((section(".data"))) uhcalltest_param_t uhctp;


#define PAGEMAP_ENTRY 8
#define GET_BIT(X,Y) (X & ((uint64_t)1<<Y)) >> Y
#define GET_PFN(X) X & 0x7FFFFFFFFFFFFF

const int __endian_bit = 1;
#define is_bigendian() ( (*(char*)&__endian_bit) == 0 )

int i, c, pid, status;
unsigned long virt_addr;
uint64_t read_val, file_offset;
char path_buf [0x100] = {};
FILE * f;
char *end;

int read_pagemap(char * path_buf, unsigned long virt_addr){
   printf("Big endian? %d\n", is_bigendian());
   f = fopen(path_buf, "rb");
   if(!f){
      printf("Error! Cannot open %s\n", path_buf);
      return -1;
   }

   //Shifting by virt-addr-offset number of bytes
   //and multiplying by the size of an address (the size of an entry in pagemap file)
   file_offset = virt_addr / getpagesize() * PAGEMAP_ENTRY;
   printf("Vaddr: 0x%lx, Page_size: %d, Entry_size: %d\n", virt_addr, getpagesize(), PAGEMAP_ENTRY);
   printf("Reading %s at 0x%llx\n", path_buf, (unsigned long long) file_offset);
   status = fseek(f, file_offset, SEEK_SET);
   if(status){
      perror("Failed to do fseek!");
      return -1;
   }
   errno = 0;
   read_val = 0;
   unsigned char c_buf[PAGEMAP_ENTRY];
   for(i=0; i < PAGEMAP_ENTRY; i++){
      c = getc(f);
      if(c==EOF){
         printf("\nReached end of the file\n");
         return 0;
      }
      if(is_bigendian())
           c_buf[i] = c;
      else
           c_buf[PAGEMAP_ENTRY - i - 1] = c;
      printf("[%d]0x%x ", i, c);
   }
   for(i=0; i < PAGEMAP_ENTRY; i++){
      //printf("%d ",c_buf[i]);
      read_val = (read_val << 8) + c_buf[i];
   }
   printf("\n");
   printf("Result: 0x%llx\n", (unsigned long long) read_val);
   //if(GET_BIT(read_val, 63))
   if(GET_BIT(read_val, 63))
      printf("PFN: 0x%llx\n",(unsigned long long) GET_PFN(read_val));
   else
      printf("Page not present\n");
   if(GET_BIT(read_val, 62))
      printf("Page swapped\n");
   fclose(f);
   return 0;
}


int main(){
	uint64_t paddr;

#if 1
	//lock uhcall_buffer in memory
	if(mlock(&uhctp, sizeof(uhctp)) == -1){
		printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
		exit(1); //nFailed to lock page in memory
	}
#endif

	read_pagemap("/proc/self/pagemap", &uhctp);

	uhcall_va2pa(&uhctp, &paddr);

	printf("from uhcall_va2pa=0x%016llx\n", paddr);

}


#if 0
int main(){
	uint8_t ch='a';
	uint32_t i;

   printf("Starting usr mode hypercall test\n");

   printf("populating uhctp.in[] and uhctp.out[]...\n");
   for(i=0; i < 16; i++)
	   uhctp.in[i] = ch + i;
   memset(&uhctp.out, 0, 16);

#if 1
	//lock uhcall_buffer in memory
	if(mlock(&uhctp, sizeof(uhctp)) == -1){
		printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
		exit(1); //nFailed to lock page in memory
	}
#endif

   printf("dumping uhctp.in[]...\n");
   for(i=0; i < 16; i++)
	   printf("%c", uhctp.in[i]);
   printf("\ndumped uhctp.in[]\n");
   printf("dumping uhctp.out[]...\n");
   for(i=0; i < 16; i++)
	   printf("%c", uhctp.out[i]);
   printf("\ndumped uhctp.out[]\n");


   printf("Proceeding to issue hypercall...\n");



   if(!uhcall(UAPP_UHCALLTEST_FUNCTION_TEST, &uhctp, sizeof(uhcalltest_param_t)))
	   printf("hypercall FAILED\n");
   else
	   printf("hypercall SUCCESS\n");

#if 1
	//unlock uhcall_buffer page
	if(munlock(&uhctp, sizeof(uhctp)) == -1){
	    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
		exit(1); //Failed to unlock page in memory
	}
#endif


   printf("dumping uhctp.in[]...\n");
   for(i=0; i < 16; i++)
	   printf("%c", uhctp.in[i]);
   printf("\ndumped uhctp.in[]\n");
   printf("dumping uhctp.out[]...\n");
   for(i=0; i < 16; i++)
	   printf("%c", uhctp.out[i]);
   printf("\ndumped uhctp.out[]\n");




   printf("End of test\n");
   return 0;
}
#endif
