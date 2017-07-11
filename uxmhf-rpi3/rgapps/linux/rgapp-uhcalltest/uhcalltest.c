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
