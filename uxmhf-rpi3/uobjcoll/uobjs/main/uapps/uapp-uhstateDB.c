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
 * Authors: Matt McCormack (<matthew.mccormack@live.com>)
 *          Amit Vasudevan (<amitvasudevan@acm.org>)
 */

/*
	uhstateDB hypapp
	guest hypercall to protected DB, containing the current and max states

        authors: matt mccormack (<matthew.mccormack@live.com>)
                 amit vasudevan (<amitvasudevan@acm.org>)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/whitelist.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uhstateDB.h>

__attribute__((section(".data"))) int32_t stateDB[MAX_STATES]={0};
__attribute__((section(".data"))) uint32_t maxStateDB[MAX_STATES]={0};
__attribute__((section(".data"))) int32_t DB_SET=0;

bool uapp_uhstateDB_handlehcall(u32  uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len)
{
  uhstatedb_param_t *uhcp;

  if((uhcall_function != UAPP_UHSTATEDB_FUNCTION_GET) && (uhcall_function != UAPP_UHSTATEDB_FUNCTION_NEXT) && (uhcall_function != UAPP_UHSTATEDB_FUNCTION_INIT))
    return false;
  
  uhcp = (uhstatedb_param_t *)uhcall_buffer;
  int i;

  //call acl function
  uapp_checkacl(sysreg_read_elrhyp());

  if(uhcall_function == UAPP_UHSTATEDB_FUNCTION_INIT) {
    if(DB_SET==0) {

      // Initialize maximum state values, based upon input
      for(i=0; i<uhcp->numStates; i++){
	maxStateDB[i]=uhcp->maxArray[i];
      }
      // only allow this to run once.
      DB_SET = 1;
    }
    return true;
  }

  if((uhcall_function == UAPP_UHSTATEDB_FUNCTION_GET) || (uhcall_function == UAPP_UHSTATEDB_FUNCTION_NEXT)) {

    #if 0
    //debug dump
    _XDPRINTFSMP_("%s: elr_hyp va=0x%08x\n", __func__, sysreg_read_elrhyp());
    #endif

    if(uhcall_function == UAPP_UHSTATEDB_FUNCTION_GET) {
      uhcp->stateVal=stateDB[uhcp->deviceID];
      return true;
    } else if(uhcall_function == UAPP_UHSTATEDB_FUNCTION_NEXT) {
      if (stateDB[uhcp->deviceID]<maxStateDB[uhcp->deviceID])  
	stateDB[uhcp->deviceID]++;
      return true;
    } else {
      return false;
    }
  }
  return false;
}
