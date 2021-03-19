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
	uapp-i2c-driver hypapp
	guest hypercall test 
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/i2c-driver.h>

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uhcalltest.h>
//#include <uberspark/include/uberspark.h>


#define MAX_LVL1_ENTRIES	4096
#define MAX_LVL2_ENTRIES	256

#define SIZEOF_LVL1_ENTRY_MAP	(1024*1024)	//each lvl1 entry maps to 1MB of memory
#define SIZEOF_LVL2_ENTRY_MAP	(1024*1024)	//each lvl1 entry maps to 1MB of memory

//secret key for HMAC
__attribute__((section(".data"))) static unsigned char uhsign_key_i2c_driver[]="super_secret_key_for_hmac";
#define UHSIGN_KEY_SIZE (sizeof(uhsign_key_i2c_driver))
#define HMAC_DIGEST_SIZE 32

/*
uint32_t va2pa(uint32_t va){
	u32 ttbcr;
	u32 ttbr0;
	u32 ttbr1;
	u32 pdbr;
	u32 *lvl1tbl;	//4096 entries
	u32 i;
	u32 lvl1tbl_index;
	u32 lvl2tbl_index;
	u32 lvl1tbl_entry;
	u32 lvl2tbl_entry;
	u32 *lvl2tbl;

	_XDPRINTFSMP_("%s: ENTER: va=0x%08x\n", __func__, va);

	ttbcr = sysreg_read_ttbcr();
	_XDPRINTFSMP_("%s: ttbcr=0x%08x\n", __func__, ttbcr);

	ttbr0 = sysreg_read_ttbr0();
	_XDPRINTFSMP_("%s: ttbr0=0x%08x\n", __func__, ttbr0);

	ttbr1 = sysreg_read_ttbr1();
	_XDPRINTFSMP_("%s: ttbr1=0x%08x\n", __func__, ttbr1);


	pdbr = ttbr0 & 0xFFFFFF80UL;	//strip lower 7 bits
	_XDPRINTFSMP_("%s: pdbr=0x%08x\n", __func__, pdbr);

	lvl1tbl_index = va/SIZEOF_LVL1_ENTRY_MAP;
	lvl2tbl_index = (va % SIZEOF_LVL1_ENTRY_MAP) / 4096;

	lvl1tbl = (u32 *)pdbr;

	_XDPRINTFSMP_("%s: lvl1tbl=0x%08x\n", __func__, lvl1tbl);

	lvl1tbl_entry = lvl1tbl[lvl1tbl_index];

	_XDPRINTFSMP_("%s: lvl1tbl_index=%u, lvl1tbl entry=0x%08x\n", __func__,
			lvl1tbl_index, lvl1tbl_entry);

	if( (lvl1tbl_entry & 0x00000003UL) != 0x1){
		_XDPRINTFSMP_("%s: unhandled lvl1tbl_entry. Halting!\n", __func__);
		HALT();
	}

	lvl2tbl = (u32 *) (u32)( lvl1tbl_entry & 0xFFFFFE00UL);

	_XDPRINTFSMP_("%s: lvl2tbl=0x%08x\n", __func__, lvl2tbl);

	lvl2tbl_entry = lvl2tbl[lvl2tbl_index];

	_XDPRINTFSMP_("%s: lvl2tbl_index=%u, lvl2tbl entry=0x%08x\n", __func__,
			lvl2tbl_index, lvl2tbl_entry);

	_XDPRINTFSMP_("%s: WiP\n", __func__);
}
*/

/*
bool va2pa(uint32_t va, u32 *pa){
	u32 par;
	u8 *ch;

	//_XDPRINTFSMP_("%s: ENTER: va=0x%08x\n", __func__, va);

	//sysreg_tlbiallh();
#if 0
	sysreg_ats12nsour(va);
	par = sysreg_read_par();
#endif

	sysreg_ats1cpr(va);
	par = sysreg_read_par();

	//_XDPRINTFSMP_("%s: PAR=0x%08x\n", __func__, par);

	if(par & 0x1)
		return false; 	//_XDPRINTFSMP_("%s: Fault in address translation. Halting!\n", __func__);

	par &= 0xFFFFF000UL;

	//_XDPRINTFSMP_("%s: PAR after pruning=0x%08x\n", __func__, par);

	*pa = par;

	//_XDPRINTFSMP_("%s: EXIT: pa=0x%08x\n", __func__, *pa);

	return true;
}

*/

//return true if handled the hypercall, false if not
bool uapp_i2c_driver_handlehcall(u32 i2c_driver_function, void *i2c_driver_buffer, u32 i2c_driver_buffer_len){
    i2c_driver_param_t *u_i2c_driver;
    unsigned long digest_size = HMAC_DIGEST_SIZE;

#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_PL011__) || defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_MINI__)
        //initialize uart
        uart_init();
#endif

    u_i2c_driver = (i2c_driver_param_t *)i2c_driver_buffer;
    _XDPRINTFSMP_("u_i2c_driver address: %x\n", u_i2c_driver);

    if (i2c_driver_function == UAPP_I2C_DRIVER_FUNCTION_TEST){
       uint32_t in_buffer_pa;
       uint32_t out_buffer_pa;
       if(!uapp_va2pa(u_i2c_driver->in_buffer_va, &in_buffer_pa) ||
          !uapp_va2pa(u_i2c_driver->out_buffer_va, &out_buffer_pa) ){
          //error, this should not happen, probably need to print a message to serial debug and halt
           _XDPRINTFSMP_("%s: Error, could not translate va2pa!\n", __func__);

        }else{
           _XDPRINTFSMP_("About to call HMAC function: \n");
           uberspark_uobjrtl_crypto__mac_hmacsha256__hmac_sha256_memory (uhsign_key_i2c_driver,  (unsigned long) UHSIGN_KEY_SIZE, (unsigned char *) in_buffer_pa, (unsigned long) u_i2c_driver->len, out_buffer_pa, &digest_size);

           return true;
        } 
	return false;
     }
}
