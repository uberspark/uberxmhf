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

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/picar-s.h>
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
#define NUM_REF 5


/* Private Functions */
void calculate_speed(int *array,int arr_len,int fw_speed,int *sp, int *st){
   const int a_step = 2;
   const int b_step = 8;
   const int c_step = 24;
   const int d_step = 40;
   if((array[0] == 0) && (array[1] == 0) && (array[2] == 1) &&
      (array[3] == 0) && (array[4] == 0) ){
      *st = 0;
   }
   else if(((array[0] == 0) && (array[1] == 1) && (array[2] == 1) &&
      (array[3] == 0) && (array[4] == 0) ) ||
      ((array[0] == 0) && (array[1] == 0) && (array[2] == 1) &&
      (array[3] == 1) && (array[4] == 0))) {
      *st =  a_step;
      *sp = fw_speed - 10;
   }
   else if(((array[0] == 0) && (array[1] == 1) && (array[2] == 0) &&
      (array[3] == 0) && (array[4] == 0) ) ||
      ((array[0] == 0) && (array[1] == 0) && (array[2] == 0) &&
      (array[3] == 1) && (array[4] == 0))) {
      *st = b_step;
      *sp = fw_speed - 15;
   }
   else if(((array[0] == 1) && (array[1] == 1) && (array[2] == 0) &&
      (array[3] == 0) && (array[4] == 0) ) ||
      ((array[0] == 0) && (array[1] == 0) && (array[2] == 0) &&
      (array[3] == 1) && (array[4] == 1))) {
      *st = c_step;
      *sp = fw_speed - 25;
   }
   else if(((array[0] == 1) && (array[1] == 0) && (array[2] == 0) &&
      (array[3] == 0) && (array[4] == 0) ) ||
      ((array[0] == 0) && (array[1] == 0) && (array[2] == 0) &&
      (array[3] == 0) && (array[4] == 1))) {
      *st = d_step;
      *sp = fw_speed - 35;
   }
   else{
      *st = d_step;
      *sp = fw_speed - 40;
   }
}


void calculate_angle(int *array,int arr_len,int *turn_angle, int st){
   if((array[0] == 0) && (array[1] == 0) && (array[2] == 1) &&
      (array[3] == 0) && (array[4] == 0) ){
      *turn_angle = 90;
   }
   else if(((array[0] == 0) && (array[1] == 1) && (array[2] == 1) &&
      (array[3] == 0) && (array[4] == 0) ) ||
      ((array[0] == 0) && (array[1] == 1) && (array[2] == 0) &&
      (array[3] == 0) && (array[4] == 0)) ||
      ((array[0] == 1) && (array[1] == 1) && (array[2] == 0) &&
      (array[3] == 0) && (array[4] == 0)) ||
      ((array[0] == 1) && (array[1] == 0) && (array[2] == 0) &&
      (array[3] == 0) && (array[4] == 0)) ) {
      *turn_angle = (int)(90 - st);
   }
   else if(((array[0] == 0) && (array[1] == 0) && (array[2] == 1) &&
      (array[3] == 1) && (array[4] == 0) ) ||
      ((array[0] == 0) && (array[1] == 0) && (array[2] == 0) &&
      (array[3] == 1) && (array[4] == 0)) ||
      ((array[0] == 0) && (array[1] == 0) && (array[2] == 0) &&
      (array[3] == 1) && (array[4] == 1)) ||
      ((array[0] == 0) && (array[1] == 0) && (array[2] == 0) &&
      (array[3] == 0) && (array[4] == 1)) ) {
      *turn_angle = (int)(90 + st);
   }
}



bool uapp_picar_s_handlehcall(u32 picar_s_function, void *picar_s_buffer, u32 picar_s_buffer_len){
 picar_s_param_t *upicar;
 unsigned long digest_size = HMAC_DIGEST_SIZE;
 upicar = (picar_s_param_t *)picar_s_buffer;
 input_params *in_params;
 output_params *out_params;

   if(picar_s_function == UAPP_PICAR_S_FUNCTION_PROT) {

     uapp_picar_s_handlehcall_prot(upicar);
     return true;

   }else if (picar_s_function == UAPP_PICAR_S_FUNCTION_UNPROT) {

     uapp_picar_s_handlehcall_unprot(upicar);
     return true;

   }else if (picar_s_function == UAPP_PICAR_S_FUNCTION_TEST){
      uint32_t encrypted_buffer_pa;
      uint32_t decrypted_buffer_pa;
      uint32_t in_params_pa;
      uint32_t out_params_pa;

      /*  	_XDPRINTFSMP_("%s: Got control: encrypted_buffer_va=0x%08x, decrypted_buffer_va=0x%08x\n",
            __func__, upicar->encrypted_buffer_va, upicar->decrypted_buffer_va);
      */

      if(!uapp_va2pa(upicar->encrypted_buffer_va, &encrypted_buffer_pa) ||
         !uapp_va2pa(upicar->decrypted_buffer_va, &decrypted_buffer_pa) ||
         !uapp_va2pa(upicar->in_params_va, &in_params_pa) ||
         !uapp_va2pa(upicar->out_params_va, &out_params_pa))
         {
         //error, this should not happen, probably need to print a message to serial debug and halt
         _XDPRINTFSMP_("%s: Error, could not translate va2pa!\n", __func__);
         return false;

      }else{
         int out_step;
         int out_speed;
         int out_turning_angle;
         in_params = (input_params *) in_params_pa;
         out_params = (output_params *) out_params_pa;
         /*       _XDPRINTFSMP_("%s: encrypted buffer va=0x%08x, pa=0x%08x\n", __func__,
                     upicar->encrypted_bu:179ffer_va, encrypted_buffer_pa);

               _XDPRINTFSMP_("%s: decrypted buffer va=0x%08x, pa=0x%08x\n", __func__,
                     upicar->decrypted_buffer_va, decrypted_buffer_pa);
         */
         uberspark_uobjrtl_crypto__mac_hmacsha256__hmac_sha256_memory (uhsign_key_picar,  (unsigned long) UHSIGN_KEY_SIZE, (unsigned char *) encrypted_buffer_pa, (unsigned long) in_params->len, decrypted_buffer_pa, &digest_size);
         calculate_speed(in_params->array,NUM_REF,in_params->speed,&out_speed,&out_step);
         calculate_angle(in_params->array,NUM_REF,&out_turning_angle,out_step);
        out_params->out_speed = out_speed;
        out_params->out_step  = out_step;
        out_params->out_turning_angle = out_turning_angle;
      }

      return true;

   }else{
      return false; //this is not our hypercall, so pass up the chain

   }
}

void uapp_picar_s_handlehcall_prot(picar_s_param_t *upicar){
   u64 roattrs;
   uint32_t buffer_pa;
   u64 prot;


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
		(LDESC_S2_S2AP_READ_ONLY << LDESC_S2_MEMATTR_S2AP_SHIFT) |
		(MEM_INNER_SHAREABLE << LDESC_S2_MEMATTR_SH_SHIFT) |
		LDESC_S2_MEMATTR_AF_MASK;

      prot=uapi_s2pgtbl_getprot(buffer_pa);
     	_XDPRINTFSMP_("%s: original pt entry=0x%016llx\n", __func__, prot);

       uapi_s2pgtbl_setprot(buffer_pa, roattrs);
       CASM_FUNCCALL(sysreg_tlbiallis, CASM_NOPARAM);
           uapp_picar_s_page_pa=buffer_pa;
           uapp_picar_s_activated=true;

      prot=uapi_s2pgtbl_getprot(buffer_pa);
     	_XDPRINTFSMP_("%s: revised pt entry=0x%016llx\n", __func__, prot);

     	_XDPRINTFSMP_("%s: setup protections: buffer_va=0x%08x, buffer_pa=0x%08x\n", __func__, upicar->buffer_va, buffer_pa);

   }
}

void uapp_picar_s_handlehcall_unprot(picar_s_param_t *upicar){
   u64 rwattrs;
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
       CASM_FUNCCALL(sysreg_tlbiallis, CASM_NOPARAM);
           uapp_picar_s_page_pa=0;
           uapp_picar_s_activated=false;

     	_XDPRINTFSMP_("%s: removed protections: buffer_va=0x%08x, buffer_pa=0x%08x\n", __func__, upicar->buffer_va, buffer_pa);

   }
}
