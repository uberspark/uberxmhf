/*
 * micro-tpm test program (utpmtest)
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

//__attribute__((aligned(4096))) static uhcalltest_param_t uhctp;

int main(){

   printf("Starting usr mode utpm test...\n");


   printf("End of utpm test\n");
   return 0;
}
