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


int main(){

   printf("Starting usr mode hypercall test: Proceeding to issue hypercall...\n");

   if(!uhcall(UAPP_UHCALLTEST_FUNCTION_TEST, NULL, 0))
	   printf("hypercall FAILED\n");
   else
	   printf("hypercall SUCCESS\n");

   printf("End of test\n");
   return 0;
}
