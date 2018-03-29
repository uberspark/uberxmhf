/*
 * hypmtscheduler test program
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
#include <hypmtscheduler.h>

__attribute__((aligned(4096))) __attribute__((section(".data"))) ugapp_hypmtscheduler_param_t hmtsp;

int main(){
    printf("%s: start\n", __FUNCTION__);

    memset(&hmtsp, 0, sizeof(hmtsp));
    hmtsp.in[0] = 'X';

    if(!uhcall(UAPP_HYPMTSCHEDULER_UHCALL, &hmtsp, sizeof(ugapp_hypmtscheduler_param_t)))
 	   printf("hypercall FAILED\n");
    else
 	   printf("hypercall SUCCESS\n");


    printf("%s: return value=%c\n", __FUNCTION__, hmtsp.out[0]);
    printf("%s: end\n", __FUNCTION__);

    return 0;
}


