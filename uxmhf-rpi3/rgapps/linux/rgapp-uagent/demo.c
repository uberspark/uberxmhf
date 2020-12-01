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
 * author: matt mccormack (<matthew.mccormack@live.com>)
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
#include <uagent.h>

__attribute__((aligned(4096))) __attribute__((section(".data"))) uagent_param_t uhcp;

void do_ucrypt(void *bufptr) {
  uagent_param_t *ptr_uhcp = (uagent_param_t *)bufptr;
  if(!uhcall(UAPP_UAGENT_FUNCTION_SIGN, ptr_uhcp, sizeof(uagent_param_t)))    
    printf("hypercall FAILED\n");
  else
    printf("SUCCESS\n");


  printf("output: ");
  uint32_t i;
  for(i=0;i<16;i++)
    printf("%02x", ptr_uhcp->pkt_data[i]);
  printf("\n");
}


int main() {
  uint8_t *data=(uint8_t *)"hello world";
  uint32_t data_len=11;

  printf("input: ");
  uint32_t i;
  for(i=0;i<data_len;i++)
    printf("%02x", data[i]);
  printf("\n");  
  
  memcpy(&uhcp.pkt_data, data, data_len); 
  uhcp.pkt_size=data_len;
  uhcp.vaddr = (uint32_t)&uhcp;
  uhcp.op=1; //encrypt

  printf("[] passing uagent_param_t to encrypt\n");

  do_ucrypt((void *)&uhcp);

  uhcp.op=2; //decrypt
  printf("[] repeating to decrypt data\n");

  do_ucrypt((void *)&uhcp);

  printf("[] test complete\n");
    
  return 0;
}
  
