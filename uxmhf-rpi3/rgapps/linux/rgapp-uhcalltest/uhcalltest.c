/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

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

#if 0

int main(){
	uint8_t ch='a';
	uint32_t i;

	if( mlockall(MCL_FUTURE) == -1){
		printf("error locking memory\n");
		exit(1);
	}

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

	if( munlockall() == -1){
		printf("error unlocking memory\n");
		exit(1);
	}


   printf("End of test\n");
   return 0;
}
#endif

#if 0
int main(){
	uhcalltest_param_t *ptr_uhctp;
	uint32_t i;
	uint8_t ch='a';

    printf("%s: start\n", __FUNCTION__);

	if (posix_memalign(&ptr_uhctp, 4096, sizeof(uhcalltest_param_t)) != 0){
	    printf("%s: error: line %u\n", __FUNCTION__);
    	exit(1);
	}


	printf("%s: populating in[] and out[]...\n", __FUNCTION__);
	for(i=0; i < 16; i++)
	   ptr_uhctp->in[i] = ch + i;
	memset(&ptr_uhctp->out, 0, 16);

	printf("dumping in[]...\n");
	for(i=0; i < 16; i++)
		printf("%c", ptr_uhctp->in[i]);
	printf("\n");

    if(!uhcall(UAPP_UHCALLTEST_FUNCTION_TEST, ptr_uhctp, sizeof(uhcalltest_param_t)))
 	   printf("hypercall FAILED\n");
    else
 	   printf("hypercall SUCCESS\n");

    printf("dumping out[]...\n");
    for(i=0; i < 16; i++)
 	   printf("%c", ptr_uhctp->out[i]);
    printf("\n");


    free(ptr_uhctp);

    printf("%s: end\n", __FUNCTION__);
    return 0;

}
#endif


void do_uhcalltest(void *bufptr){
	uhcalltest_param_t *ptr_uhctp = (uhcalltest_param_t *)bufptr;
	uint32_t i;
	uint8_t ch='a';

    printf("%s: start\n", __FUNCTION__);

	printf("%s: populating in[] and out[]...\n", __FUNCTION__);
	for(i=0; i < 16; i++)
	   ptr_uhctp->in[i] = ch + i;
	memset(&ptr_uhctp->out, 0, 16);

	printf("dumping in[]...\n");
	for(i=0; i < 16; i++)
		printf("%c", ptr_uhctp->in[i]);
	printf("\n");

    if(!uhcall(UAPP_UHCALLTEST_FUNCTION_TEST, ptr_uhctp, sizeof(uhcalltest_param_t)))
 	   printf("hypercall FAILED\n");
    else
 	   printf("hypercall SUCCESS\n");

    printf("dumping out[]...\n");
    for(i=0; i < 16; i++)
 	   printf("%c", ptr_uhctp->out[i]);
    printf("\n");

    printf("%s: end\n", __FUNCTION__);
}


int main(){
	uhcalltest_param_t *ptr_uhctp;

    printf("starting uhcalltest (with static buffer)...\n");
	do_uhcalltest((void *)&uhctp);
    printf("end uhcalltest (with static buffer)...\n");

    printf("starting uhcalltest (with dynamic buffer)...\n");

	if (posix_memalign(&ptr_uhctp, 4096, sizeof(uhcalltest_param_t)) != 0){
	    printf("%s: error: line %u\n", __FUNCTION__);
    	exit(1);
	}

	do_uhcalltest((void *)ptr_uhctp);

    free(ptr_uhctp);

    printf("end uhcalltest (with dynamic buffer)...\n");

    return 0;
}


