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
	i2c-ioaccess uapp
	low-level i2c driver uapp (i2c-bcm2708) 
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/i2c-ioaccess.h>

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/i2c-ioaccess.h>

#include <uberspark/uobjrtl/crypto/include/mac/hmacsha256/hmacsha256.h>
#include <uberspark/uobjrtl/crypto/include/basedefs.h>


//secret key for HMAC
__attribute__((section(".data"))) static unsigned char uhsign_key_i2c_driver[]="super_secret_key_for_hmac";
#define UHSIGN_KEY_SIZE (sizeof(uhsign_key_i2c_driver))
#define HMAC_DIGEST_SIZE 32

//buffer for burst reads and computing hmac on it
__attribute__((section(".data"))) static unsigned char static_buffer[1024];


__attribute__((section(".data"))) unsigned char l_digest_array[HMAC_DIGEST_SIZE];
__attribute__((section(".data"))) unsigned long l_digest_size = HMAC_DIGEST_SIZE;


// this is from BCM ARM peripherals data-sheet and initial debugging
// of i2c-bcm2708 which seems to use this base. The data sheet talks about
// two more BSC master units at different addresses
// TBD: take this in via a hypercall that is called during kernel module
// initialization (presumably during ioremap)
#define I2C_BSC_BASE 0x3f804000


/* BSC register offsets */
#define BSC_C			0x00
#define BSC_S			0x04
#define BSC_DLEN		0x08
#define BSC_A			0x0c
#define BSC_FIFO		0x10
#define BSC_DIV			0x14
#define BSC_DEL			0x18
#define BSC_CLKT		0x1c

/* Bitfields in BSC_C */
#define BSC_C_I2CEN		0x00008000
#define BSC_C_INTR		0x00000400
#define BSC_C_INTT		0x00000200
#define BSC_C_INTD		0x00000100
#define BSC_C_ST		0x00000080
#define BSC_C_CLEAR_1		0x00000020
#define BSC_C_CLEAR_2		0x00000010
#define BSC_C_READ		0x00000001

/* Bitfields in BSC_S */
#define BSC_S_CLKT		0x00000200
#define BSC_S_ERR		0x00000100
#define BSC_S_RXF		0x00000080
#define BSC_S_TXE		0x00000040
#define BSC_S_RXD		0x00000020
#define BSC_S_TXD		0x00000010
#define BSC_S_RXR		0x00000008
#define BSC_S_TXW		0x00000004
#define BSC_S_DONE		0x00000002
#define BSC_S_TA		0x00000001


/* translate virtual address to physical address with offsets preserved */
bool uapp_va2pa_withoff(uint32_t va, u32 *pa){
  u32 par;
  u32 offset;

  CASM_FUNCCALL(sysreg_ats1cpr, va);
  par=CASM_FUNCCALL(sysreg_read_par, CASM_NOPARAM);

  if(par & 0x1)
    return false;

 offset = (u32)va & 0x00000FFFUL;
 par &= 0xFFFFF000UL;
 par |= offset;

   *pa = par;
  return true;
}


//return true if handled the hypercall, false if not
bool uapp_i2c_ioaccess_handle_fast_hcall(arm8_32_regs_t *r){
	uint32_t fn;
	uint32_t mmio_pa=0;
	
	fn = r->r0;	

#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_PL011__) || defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_MINI__)
        //initialize uart
        uart_init();
#endif


	if(fn == UAPP_I2C_IOACCESS_WRITEL){
		//r->r1 = input addresss
		//r->r2 = input value
		//if(!uapp_va2pa_withoff(r->r1, &mmio_pa)){
			//error, this should not happen, print a message to serial debug and halt
		//	_XDPRINTFSMP_("%s: WRITEL: Error, could not translate va2pa. halting!\n", __func__);
		//	while(1);
		//}	

		mmio_pa = (u32)I2C_BSC_BASE | ((u32)r->r1 & 0x00000FFFUL);

		_XDPRINTFSMP_("%s: WRITEL: addr=0x%08x, val=0x%08x\n", __func__, mmio_pa, r->r2);
		mmio_write32(mmio_pa, r->r2);
		return true;
	
	}else if(fn == UAPP_I2C_IOACCESS_READL){
		//r->r1 = input addresss
		//r->r2 = output value
	
		//#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_PL011__) || defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_MINI__)
	    //    //initialize uart
	  	//    uart_init();
		//#endif

		//_XDPRINTFSMP_("%s: coming in: r1(addr)=0x%08x, r2(value)=0x%08x\n", __func__,
		//	r->r1, r->r2);

		//if(!uapp_va2pa_withoff(r->r1, &mmio_pa)){
		//	//error, this should not happen, print a message to serial debug and halt
		//	_XDPRINTFSMP_("%s: READL: Error, could not translate va2pa. halting!\n", __func__);
		//	while(1);
		//}	

		//_XDPRINTFSMP_("%s: revised: r1(addr)=0x%08x, r2(value)=0x%08x\n", __func__,
		//	mmio_pa, r->r2);

		mmio_pa = (u32)I2C_BSC_BASE | ((u32)r->r1 & 0x00000FFFUL);

		r->r2 = mmio_read32(mmio_pa);

		_XDPRINTFSMP_("%s: READL: addr=0x%08x, val=0x%08x\n", __func__, mmio_pa, r->r2);

		//_XDPRINTFSMP_("%s: going out: r1(addr)=0x%08x, r2(value)=0x%08x\n", __func__,
		//	mmio_pa, r->r2);

		return true;

	} else if (fn== UAPP_I2C_IOACCESS_HMAC){
		//r->r1 = destination buffer
		//r->r2 = msg_size
	    uint32_t out_buffer_pa;
		uint32_t msg_size = r->r2;

		_XDPRINTFSMP_("%s: HMAC: buffer va=0x%08x, size=0x%08x\n", __func__, 
			r->r1, msg_size);

	    if(!uapp_va2pa(r->r1, &out_buffer_pa)){
          	//error, this should not happen, halt!
        	_XDPRINTFSMP_("%s: Error, could not translate va2pa!\n", __func__);
			return true;
        }

		if(uberspark_uobjrtl_crypto__mac_hmacsha256__hmac_sha256_memory (uhsign_key_i2c_driver,  (unsigned long) UHSIGN_KEY_SIZE, (unsigned char *) static_buffer, (unsigned long) msg_size, l_digest_array, &l_digest_size) != CRYPT_OK ){
          	//error, this should not happen, halt!
        	_XDPRINTFSMP_("%s: Error, could not compute HMAC!\n", __func__);
			return true;
		}
		
		//copy over the sensor read buffer first
		uberspark_uobjrtl_crt__memcpy(out_buffer_pa,
			static_buffer,msg_size);

		//now copy the HAC digest
		uberspark_uobjrtl_crt__memcpy(out_buffer_pa+msg_size,
			l_digest_array,HMAC_DIGEST_SIZE);


		_XDPRINTFSMP_("%s: HMAC: computed, buffer(va=0x%08x, pa=0x%08x), size=0x%08x\n", 
			__func__, r->r1, out_buffer_pa, msg_size);

		return true;

	} else if (fn== UAPP_I2C_IOACCESS_READBUFFER){
		//r->r1 = bi_pos
		//r->r2 = bi_msg_len
		//output: r->r1 = updated position
		uint32_t bi_pos = r->r1;
		uint32_t bi_msg_len = r->r2;
		uint32_t i;

		i = bi_pos;

		_XDPRINTFSMP_("%s: READBUFFER: bi_pos=0x%08x, bi_msg_len=0x%08x\n", 
			__func__, bi_pos, bi_msg_len);


		while ((i < bi_msg_len) && (mmio_read32(I2C_BSC_BASE + BSC_S) & BSC_S_RXD)){
			static_buffer[i++] = mmio_read32(I2C_BSC_BASE + BSC_FIFO);
		}

		r->r1 = i;

		_XDPRINTFSMP_("%s: READBUFFER: bi_pos=0x%08x, bi_msg_len=0x%08x, result=0x%08x\n", 
			__func__, bi_pos, bi_msg_len, r->r1);

		return true;


	}else 
		return false;
}

