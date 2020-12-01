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
 * Author: Matt McCormack (matthew.mccormack@live.com)
 *
 */

/*
 * hypercall program (uagent)
 * author: matt mccormack (<matthew.mccormack@live.com>)
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

#include <netdb.h>
#include <string.h>
#include <sys/socket.h>

#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>

#include <uhcall.h>
#include <uagent.h>

#define MAX_DATA 80
#define PORT 54321
#define SA struct sockaddr

__attribute__((aligned(4096))) __attribute__((section(".data"))) uagent_param_t uhcp;

void do_ucrypt(void *bufptr) {
  uagent_param_t *ptr_uhcp = (uagent_param_t *)bufptr;
  if(!uhcall(UAPP_UAGENT_FUNCTION_SIGN, ptr_uhcp, sizeof(uagent_param_t)))
    printf("hypercall FAILED\n");
  /*
  printf("output: ");
  uint32_t i;
  for(i=0;i<ptr_uhcp->pkt_size;i++)
    printf("%02x", ptr_uhcp->pkt_data[i]);
  printf("\n");
  */
}

int cryptLen(int in_len){
  int numBlocks=in_len/16;
  if(in_len%16)
    numBlocks++;
  return numBlocks*16;
}

void func(int sockfd) {
  char buff[MAX_DATA];
  char encBuff[MAX_DATA];
  char decBuff[MAX_DATA];    
  int n;
  uhcp.vaddr = (uint32_t)&uhcp;
  
  for(;;) {
    bzero(buff, sizeof(buff));
    bzero(encBuff, sizeof(encBuff));
    bzero(decBuff, sizeof(decBuff));
    memset(&uhcp.pkt_data, 0,  1600);    
    printf("Enter text : ");
    n=0;
    
    while((buff[n++]=getchar())!='\n');
    memcpy(&uhcp.pkt_data, buff, n); 
    uhcp.pkt_size=n;
    uhcp.op=1; //encrypt
    do_ucrypt((void *)&uhcp);
    memcpy(&encBuff[4], &uhcp.pkt_data, cryptLen(uhcp.pkt_size));
    encBuff[0]=cryptLen(uhcp.pkt_size);

    /*
    int i;
    printf("sending...");
    for(i=0; i<(uhcp.pkt_size); i++)
      printf("%02x", encBuff[i+4]);
    printf("\n");
    */
    
    write(sockfd, encBuff, cryptLen(uhcp.pkt_size)+4);
    if((strncmp(buff, "exit", 4))==0){
      printf("Client Exit...\n");
      break;
    }
    
    bzero(buff, sizeof(buff));
    bzero(encBuff, sizeof(encBuff));
    bzero(decBuff, sizeof(decBuff));    
    memset(&uhcp.pkt_data, 0,  1600);
    
    read(sockfd, encBuff, sizeof(encBuff));

    /*
    printf("received...");
    for(i=0; i<encBuff[0]; i++)
      printf("%02x", encBuff[i+4]);
    printf("\n");
    */
    
    memcpy(&uhcp.pkt_data, &encBuff[4], encBuff[0]); 
    uhcp.pkt_size=encBuff[0];
    uhcp.op=2; //decrypt
    do_ucrypt((void *)&uhcp);
    memcpy(&decBuff[4], &uhcp.pkt_data, uhcp.pkt_size);
    decBuff[0]=uhcp.pkt_size;
    memcpy(buff, &decBuff[4], (uint32_t) decBuff[0]);

    printf("From Server : %s", buff);
    if ((strncmp(buff, "exit", 4))==0){
      printf("Server sent Exit...\n");
      break;
    }
  }
}


int main() {
  int sockfd;
  struct sockaddr_in servaddr;

  sockfd = socket (AF_INET, SOCK_STREAM, 0);
  if(sockfd==-1){
    printf("socket creation failed...\n");
    exit(0);
  }
  else
    printf("Socket successfully created.\n");
  bzero(&servaddr, sizeof(servaddr));

  servaddr.sin_family=AF_INET;
  servaddr.sin_addr.s_addr=inet_addr("10.1.1.2");
  servaddr.sin_port=htons(PORT);

  if(connect(sockfd, (SA*)&servaddr, sizeof(servaddr))!=0){
    printf("connection with the server failed...\n");
    exit(0);
  }
  else
    printf("connected to the server.\n");
  
  func(sockfd);
  
  close(sockfd);
}
  
