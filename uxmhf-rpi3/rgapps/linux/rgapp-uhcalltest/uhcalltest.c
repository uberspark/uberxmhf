/*
 * hypercall test program (uhcalltest)
 * author: amit vasudevan (amitvasudevan@acm.org)
 *
 */

#include<stdio.h>
#include<stdlib.h>
#include<errno.h>
#include<fcntl.h>
#include<string.h>
#include<unistd.h>


int main(){
   int ret, fd;

   printf("Starting usr mode hypercall test...\n");

   // Open the device with read/write access
   fd = open("/dev/uhcallkmod", O_RDWR);
   if (fd < 0){
      perror("Failed to open /dev/uhcallkmod...");
      return errno;
   }

   ret = write(fd, NULL, 1);
   if (ret < 0){
      perror("Failed to write the message to the device.");
      return errno;
   }

   printf("End of test\n");
   return 0;
}
