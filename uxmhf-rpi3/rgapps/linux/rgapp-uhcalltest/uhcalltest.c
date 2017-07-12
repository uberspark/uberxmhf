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
#include <sys/mman.h>

#include <uhcall.h>
#include <uhcalltest.h>

__attribute__((aligned(4096))) __attribute__((section(".data"))) uhcalltest_param_t uhctp;

#if 1

int main(){
	uint8_t ch='a';
	uint32_t i;

   printf("Starting usr mode hypercall test\n");

   printf("populating uhctp.in[] and uhctp.out[]...\n");
   for(i=0; i < 16; i++)
	   uhctp.in[i] = ch + i;
   memset(&uhctp.out, 0, 16);

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

#if 0
int main(){
	uint8_t ch='a';
	uint64_t paddr;
	uhcalltest_param_t *myptr;
    int fd = 0;

	uhctp.in[0] = ch;

    if(mlock(&uhctp, sizeof(&uhctp)) == -1){
	    printf("%s: error: line %u\n", __FUNCTION__);
    	exit(1);
    }

    //get buffer physical address
    if(!uhcall_va2pa(&uhctp, &paddr) ){
	    printf("%s: error: line %u\n", __FUNCTION__);
    	exit(1);
    }

    printf("%s: paddr=0x%016llx\n", __FUNCTION__, paddr);

    fd = open("/dev/mem", O_RDWR|O_SYNC);
    myptr = (uhcalltest_param_t *)mmap(0, getpagesize(),
    		PROT_READ|PROT_WRITE,
			MAP_SHARED, fd, (uint32_t)paddr);


    printf("%s: char=%c\n", __FUNCTION__, myptr->in[0]);


    if(munlock(&uhctp, sizeof(&uhctp)) == -1){
	    printf("%s: error: line %u\n", __FUNCTION__);
    	exit(1);
    }
}
#endif
