/*
 * mavlinkserhb user-mode application
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

#include "../../../include/mavlinkserhb.h"

//////
// function to communicate with kernel-module
//////
void kmod_comms(unsigned int function){
	int ret, fd;

	//open device
	fd = open("/dev/mavlinkserhbkmod", O_RDWR);
	if (fd < 0){
	    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
		exit(1); //Failed to open
	}

	ret = write(fd, NULL, function);
	if (ret < 0){
	    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
		exit(1);	//error in write
	}

	if ( close(fd) < 0 ){
	    printf("%s: error: line %u\n", __FUNCTION__, __LINE__);
		exit(1);	//error in closing uhcallkmod device
	}
}


//////
// main function
//////
int main(int argc, char *argv[]){
    unsigned int testcase_num;
	printf("%s: start\n", __FUNCTION__);

	kmod_comms(UAPP_MAVLINKSERHB_UHCALL_INITIALIZE);

    printf("%s: end\n", __FUNCTION__);
    return 0;
}


