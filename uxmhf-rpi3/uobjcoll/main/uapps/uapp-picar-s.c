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
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*
	picar-s hypapp
	guest picar-s test 
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/debug.h>

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/main/include/picar-s.h>
//#include <uberspark/include/uberspark.h>
#include <uberspark/uobjrtl/crypto/include/mac/hmacsha256/hmacsha256.h>
#include <uberspark/uobjrtl/crypto/include/basedefs.h>
#include <uberspark/uobjrtl/crt/include/string.h>

#define MAX_LVL1_ENTRIES	4096
#define MAX_LVL2_ENTRIES	256

#define SIZEOF_LVL1_ENTRY_MAP	(1024*1024)	//each lvl1 entry maps to 1MB of memory
#define SIZEOF_LVL2_ENTRY_MAP	(1024*1024)	//each lvl1 entry maps to 1MB of memory

//secret key for HMAC
__attribute__((section(".data"))) static unsigned char uhsign_key_picar[]="super_secret_key_for_hmac";
__attribute__((section(".data"))) uint32_t uapp_picar_s_page_pa=0;
__attribute__((section(".data"))) bool uapp_picar_s_activated=false;

#define UHSIGN_KEY_SIZE (sizeof(uhsign_key_picar))
#define HMAC_DIGEST_SIZE 32

bool uapp_picar_s_handlehcall(u32 picar_s_function, void *picar_s_buffer, u32 picar_s_buffer_len){
 picar_s_param_t *upicar;
 unsigned long digest_size = HMAC_DIGEST_SIZE;
 upicar = (picar_s_param_t *)picar_s_buffer;

  if(picar_s_function == UAPP_PICAR_S_FUNCTION_PROT) {

     uapp_picar_s_handlehcall_prot(upicar);
     return true;

  }else if (picar_s_function == UAPP_PICAR_S_FUNCTION_UNPROT) {

     uapp_picar_s_handlehcall_unprot(upicar);
     return true;

  }else if (picar_s_function == UAPP_PICAR_S_FUNCTION_TEST){
    uint32_t encrypted_buffer_pa;
    uint32_t decrypted_buffer_pa;

  	_XDPRINTFSMP_("%s: Got control: encrypted_buffer_va=0x%08x, decrypted_buffer_va=0x%08x\n", 
      __func__, upicar->encrypted_buffer_va, upicar->decrypted_buffer_va);


    if(!uapp_va2pa(upicar->encrypted_buffer_va, &encrypted_buffer_pa) ||
       !uapp_va2pa(upicar->decrypted_buffer_va, &decrypted_buffer_pa) ){
       //error, this should not happen, probably need to print a message to serial debug and halt
     	_XDPRINTFSMP_("%s: Error, could not translate va2pa!\n", __func__);

     }else{

        _XDPRINTFSMP_("%s: encrypted buffer va=0x%08x, pa=0x%08x\n", __func__,
            upicar->encrypted_buffer_va, encrypted_buffer_pa);

        _XDPRINTFSMP_("%s: decrypted buffer va=0x%08x, pa=0x%08x\n", __func__,
            upicar->decrypted_buffer_va, decrypted_buffer_pa);

        uberspark_uobjrtl_crypto__mac_hmacsha256__hmac_sha256_memory (uhsign_key_picar,  (unsigned long) UHSIGN_KEY_SIZE, (unsigned char *) encrypted_buffer_pa, (unsigned long) upicar->len, decrypted_buffer_pa, &digest_size);

        return true;

      } 
      return false;
   }
}

void uapp_picar_s_handlehcall_prot(picar_s_param_t *upicar){
   uint32_t roattrs;
   uint32_t buffer_pa;

#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_PL011__) || defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_MINI__)
	//initialize uart
	uart_init();
#endif
   
  	_XDPRINTFSMP_("%s: Got control: buffer_va=0x%08x...\n", __func__, upicar->buffer_va);

   if(!uapp_va2pa(upicar->buffer_va, &buffer_pa)){
       //error, this should not happen, probably need to print a message to serial debug and halt
     	_XDPRINTFSMP_("%s: Error, could not translate va2pa!\n", __func__);

   }else{
      roattrs = 
      (LDESC_S2_MC_OUTER_WRITE_BACK_CACHEABLE_INNER_WRITE_BACK_CACHEABLE << LDESC_S2_MEMATTR_MC_SHIFT) |
		(LDESC_S2_S2AP_READ_WRITE << LDESC_S2_MEMATTR_S2AP_SHIFT) |
		(MEM_INNER_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
		LDESC_S2_MEMATTR_AF_MASK;

       uapi_s2pgtbl_setprot(buffer_pa, roattrs);
       sysreg_tlbiallis();
           uapp_picar_s_page_pa=buffer_pa;
           uapp_picar_s_activated=true;

     	_XDPRINTFSMP_("%s: setup protections: buffer_va=0x%08x, buffer_pa=0x%08x\n", __func__, upicar->buffer_va, buffer_pa);

   }
}

void uapp_picar_s_handlehcall_unprot(picar_s_param_t *upicar){
   uint32_t rwattrs;
   uint32_t buffer_pa;

  	_XDPRINTFSMP_("%s: Got control: buffer_va=0x%08x...\n", __func__, upicar->buffer_va);

   if(!uapp_va2pa(upicar->buffer_va, &buffer_pa)){
       //error, this should not happen, probably need to print a message to serial debug and halt
     	_XDPRINTFSMP_("%s: Error, could not translate va2pa!\n", __func__);

   }else{
      rwattrs = 
      (LDESC_S2_MC_OUTER_WRITE_BACK_CACHEABLE_INNER_WRITE_BACK_CACHEABLE << LDESC_S2_MEMATTR_MC_SHIFT) |
		(LDESC_S2_S2AP_READ_WRITE << LDESC_S2_MEMATTR_S2AP_SHIFT) |
		(MEM_INNER_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
		LDESC_S2_MEMATTR_AF_MASK;

       uapi_s2pgtbl_setprot(buffer_pa, rwattrs);
       sysreg_tlbiallis();
           uapp_picar_s_page_pa=0;
           uapp_picar_s_activated=false;

     	_XDPRINTFSMP_("%s: removed protections: buffer_va=0x%08x, buffer_pa=0x%08x\n", __func__, upicar->buffer_va, buffer_pa);

   }
}

