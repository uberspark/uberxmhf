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
 * hypercall program (uhstateDB)
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
#include <uhstateDB.h>

__attribute__((aligned(4096))) __attribute__((section(".data"))) uhstatedb_param_t uhcp;

void init(void *bufptr) {
  uhstatedb_param_t *ptr_uhcp = (uhstatedb_param_t *)bufptr;
  if(!uhcall(UAPP_UHSTATEDB_FUNCTION_INIT, ptr_uhcp, sizeof(uhstatedb_param_t)))    
    printf("hypercall FAILED\n");
  else {
    printf("SUCCESS\n");
    printf("stateDB initialized\n");
  }    
}

void get(void *bufptr) {
  uhstatedb_param_t *ptr_uhcp = (uhstatedb_param_t *)bufptr;
  if(!uhcall(UAPP_UHSTATEDB_FUNCTION_GET, ptr_uhcp, sizeof(uhstatedb_param_t)))
    printf("hypercall FAILED\n");
  else {
    printf("SUCCESS\n");
    printf("State value for device: %d, -- %d\n", ptr_uhcp->deviceID, ptr_uhcp->stateVal);
  }
}

void next(void *bufptr) {
  uhstatedb_param_t *ptr_uhcp = (uhstatedb_param_t *)bufptr;
  if(!uhcall(UAPP_UHSTATEDB_FUNCTION_NEXT, ptr_uhcp, sizeof(uhstatedb_param_t)))
    printf("hypercall FAILED\n");
  else {
    printf("SUCCESS\n");
    printf("stateDB value udated\n");
  }
}


int main() {
  uint32_t numDevices=3;
  uint32_t maxArray[numDevices];
  int i;
  for(i=0;i<numDevices; i++) {
    maxArray[i]=2*i+1;
  }

  memcpy(&uhcp.maxArray, maxArray, sizeof(maxArray)); 
  uhcp.numStates=numDevices;
  uhcp.vaddr = (uint32_t)&uhcp;

  printf("[] passing uhstateDB_param_t to init\n");
  init((void *)&uhcp);

  uhcp.deviceID=0;
  printf("[] getting state value for device %d \n", uhcp.deviceID);
  get((void *)&uhcp);

  uhcp.deviceID=1;
  printf("[] transitioning state value for device %d \n", uhcp.deviceID);
  get((void *)&uhcp);
  next((void *)&uhcp);
  get((void *)&uhcp);

  uhcp.deviceID=0;  
  printf("[] attempting to transitioning state value for device %d above it's max (to 3, max is 1) \n", uhcp.deviceID);
  next((void *)&uhcp);
  next((void *)&uhcp);
  next((void *)&uhcp);  
  get((void *)&uhcp);

  uhcp.deviceID=2;  
  printf("[] transitioning state value for device %d to 3 (max is 5) \n", uhcp.deviceID);
  printf("  -- initial value");
  get((void *)&uhcp);   
  next((void *)&uhcp);
  next((void *)&uhcp);
  next((void *)&uhcp);
  printf("  -- final value");  
  get((void *)&uhcp); 
  
  printf("[] test complete\n");
    
  return 0;
}
  
