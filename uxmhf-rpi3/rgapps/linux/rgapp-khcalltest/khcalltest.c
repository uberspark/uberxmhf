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
 * hypercall test program (khcalltest)
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
#include <khcalltest.h>

__attribute__((aligned(4096))) __attribute__((section(".data"))) khcalltest_param_t khctp;



void do_khcalltest(void *bufptr){
    khcalltest_param_t *ptr_khctp = (khcalltest_param_t *)bufptr;
    uint32_t i;
    uint8_t ch='a';

    printf("%s: start\n", __FUNCTION__);

    printf("%s: populating in[] and out[]...\n", __FUNCTION__);
    for(i=0; i < 16; i++)
       ptr_khctp->in[i] = ch + i;
    memset(&ptr_khctp->out, 0, 16);

    printf("dumping in[]...\n");
    for(i=0; i < 16; i++)
      printf("%c", ptr_khctp->in[i]);
    printf("\n");

    if(!uhcall(UAPP_KHCALLTEST_FUNCTION_TEST, ptr_khctp, sizeof(khcalltest_param_t)))
 	   printf("hypercall FAILED\n");
    else
 	   printf("hypercall SUCCESS\n"); 

    printf("dumping out[]...\n");
    for(i=0; i < 16; i++)
 	   printf("%c", ptr_khctp->out[i]);
    printf("\n");

    printf("%s: end\n", __FUNCTION__);
}


int main(){
    khcalltest_param_t *ptr_khctp;

    printf("starting khcalltest (with static buffer)...\n");
	do_khcalltest((void *)&khctp);
    printf("end khcalltest (with static buffer)...\n");

    printf("starting khcalltest (with dynamic buffer)...\n");

    if (posix_memalign((void **)&ptr_khctp, 4096, sizeof(khcalltest_param_t)) != 0){
	    printf("%s: error: line %u\n", __FUNCTION__ , __LINE__);
    	exit(1);
    }

    do_khcalltest((void *)ptr_khctp);

    free(ptr_khctp);

    printf("end khcalltest (with dynamic buffer)...\n");

    return 0;
}


