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
 * hypercall program (uhsign)
 * author: matt mccormack (matthew.mccormack@live.com)
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
#include <uhsign.h>

#include <xmhfcrypto.h>
#include <hmac-sha1.h>

#include <sys/time.h>

__attribute__((aligned(4096))) __attribute__((section(".data"))) uhsign_param_t uhcp;

__attribute__((section(".data"))) unsigned char key[]="super_secret_key_for_hmac";
#define USER_KEY_SIZE (sizeof(key))

void do_uhsign(uint8_t *pkt, uint32_t pkt_size) {
  memcpy(&uhcp.pkt, pkt, pkt_size); 
  uhcp.pkt_size=pkt_size;
  uhsign_param_t *uhcp_ptr = &uhcp;
  
  if(!uhcall(UAPP_UHSIGN_FUNCTION_SIGN, uhcp_ptr, sizeof(uhsign_param_t)))
    printf("hypercall FAILED\n");
  else
    printf("SUCCESS\n");

  printf("Digest: ");
  uint32_t i;
  for(i=0;i<20;i++)
    printf("%02x", uhcp_ptr->digest[i]);
  printf("\n");

}

void do_uhsign1(void *bufptr) {
  uhsign_param_t *ptr_uhcp = (uhsign_param_t *)bufptr;

  if(!uhcall(UAPP_UHSIGN_FUNCTION_SIGN, ptr_uhcp, sizeof(uhsign_param_t)))
    printf("hypercall FAILED\n");
  else
    printf("SUCCESS\n");


  printf("Digest: ");
  uint32_t i;
  for(i=0;i<20;i++)
    printf("%02x", ptr_uhcp->digest[i]);
  printf("\n");

}


int main() {
  struct timeval tv1, tv2;
  //clock_t begin = clock();
  gettimeofday(&tv1, NULL);
  uint8_t *data=(uint8_t *)"hello world";
  uint32_t data_len=11;
  memcpy(&uhcp.pkt, data, data_len); 
  uhcp.pkt_size=data_len;

  printf("[] passing uhsign_param_t\n");

  do_uhsign1((void *)&uhcp);

  /* moving uapp actions into userspace for benchmarking */
  /*
  unsigned long digest_size=20;
  unsigned char *digest=NULL;
  int i;
  uint8_t output[20];
  if(hmac_sha1_memory(key, (unsigned long) USER_KEY_SIZE, (unsigned char *) data, (unsigned long) data_len, digest, &digest_size)==CRYPT_OK) {
    for(i=0;i<digest_size;i++)
      output[i]=(uint8_t)*(digest+i);
    printf("%02x", output[i]);
  }
  printf("\n");
  */
    

  printf("\n");

  memset(&uhcp.pkt, 0, data_len);
  
  printf("[] passing pointer to data\n");

  do_uhsign(data, data_len);

  printf("demo complete, thanks for your time\n");


  //clock_t end = clock();
  gettimeofday(&tv2, NULL);
  //double time_spend = (double)(end-begin) / CLOCKS_PER_SEC;
  printf("Total time = %f seconds\n", (double) (tv2.tv_usec-tv1.tv_usec)/1000000 + (double) (tv2.tv_sec - tv1.tv_sec));
  return 0;
}
  
