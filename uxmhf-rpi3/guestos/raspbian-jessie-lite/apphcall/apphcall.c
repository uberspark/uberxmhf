#include<stdio.h>
#include<stdlib.h>
#include<errno.h>
#include<fcntl.h>
#include<string.h>
#include<unistd.h>


int main(){
   int ret, fd;

   printf("Starting usr mode hypercall test...\n");

   fd = open("/dev/hypcallchar", O_RDWR);             // Open the device with read/write access
   if (fd < 0){
      perror("Failed to open the device...");
      return errno;
   }

   ret = write(fd, NULL, 0);
   if (ret < 0){
      perror("Failed to write the message to the device.");
      return errno;
   }

   printf("End of test\n");
   return 0;
}
