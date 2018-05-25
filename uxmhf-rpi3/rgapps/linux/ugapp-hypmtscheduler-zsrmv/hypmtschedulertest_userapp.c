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

//#include <hypmtscheduler.h>


void test_createhyptask(void){

}

void test_disablehyptask(void){

}

void test_deletehyptask(void){

}


int main(int argc, char *argv[]){
    unsigned int testcase_num;
	printf("%s: start\n", __FUNCTION__);

    if(argc != 2){
  	   printf("usage: ugapp-hypmtschedulertest <testcasenum>\n");
  	   exit(1);
    }

    testcase_num = atoi(argv[1]);

	printf("%s: testcase_num=%u\n", __FUNCTION__, testcase_num);

	switch(testcase_num){
	case 0:
		test_createhyptask();
		break;

	case 1:
		test_disablehyptask();
		break;

	case 2:
		test_deletehyptask();
		break;

	default:
		printf("%s: unknown testcase_num=%u, exiting!\n", __FUNCTION__, testcase_num);
		exit(1);
	}


    printf("%s: end-of-test\n", __FUNCTION__);
    return 0;
}


