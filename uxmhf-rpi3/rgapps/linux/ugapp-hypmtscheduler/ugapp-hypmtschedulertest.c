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

    hmtsp.uhcall_fn = UAPP_HYPMTSCHEDULER_UHCALL_FNCREATEHYPTHREAD;
    hmtsp.iparam_1 = 9 * 20 * 1024 * 1024;	//~9 sec period first time
    hmtsp.iparam_2 = 9 * 20 * 1024 * 1024;	//~9 sec period thereafter
    hmtsp.iparam_3 = 3;						//priority=1

    if(!uhcall(UAPP_HYPMTSCHEDULER_UHCALL, &hmtsp, sizeof(ugapp_hypmtscheduler_param_t)))
 	   printf("hypercall FAILED\n");
    else
 	   printf("hypercall SUCCESS\n");

    printf("%s: return status=%u\n", __FUNCTION__, hmtsp.status);
    printf("%s: end\n", __FUNCTION__);

    return 0;
}


