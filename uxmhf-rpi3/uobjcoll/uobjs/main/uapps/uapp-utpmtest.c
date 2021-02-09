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
	uhcalltest hypapp
	guest hypercall test hypapp
	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/types.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/arm8-32.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/bcm2837.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/uart.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/debug.h>

#include <uberspark/uobjrtl/crypto/include/basedefs.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/libutpm/utpm.h>
#include <uberspark/uobjcoll/platform/rpi3/uxmhf/uobjs/main/include/utpmtest.h>
//#include <uberspark/include/uberspark.h>


//return true if handled the hypercall, false if not
bool uapp_utpmtest_handlehcall(u32 uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len){
	utpmtest_param_t *utpmtest_param = 	(utpmtest_param_t *)uhcall_buffer;

	//_XDPRINTFSMP_("%s: uhcall_function=%x, uhcall_buffer=0x%08x, uhcall_buffer_len=%u\n",
	//		__func__, uhcall_function, uhcall_buffer, uhcall_buffer_len);

#if 0
	if(utpmtest_param->magic != 0xDEADBEEF){
		_XDPRINTFSMP_("%s: invalid magic -- check buffer locking!\n",
				__func__);

	}
#endif

	if(uhcall_function == UAPP_UTPM_FUNCTION_INIT_MASTER_ENTROPY){
		//_XDPRINTFSMP_("%s: INIT_MASTER_ENTROPY: magic=0x%08x\n",
		//		__func__, utpmtest_param->magic);


		#if 1
		utpmtest_param->result =
				utpm_init_master_entropy(&utpmtest_param->g_aeskey,
						&utpmtest_param->g_hmackey,
						&utpmtest_param->g_rsakey);
		#endif

		return true;

	} else	if(uhcall_function == UAPP_UTPM_FUNCTION_INIT_INSTANCE){

			utpm_init_instance(&utpmtest_param->utpm);

			return true;

	} else	if(uhcall_function == UAPP_UTPM_FUNCTION_PCRREAD){

			utpmtest_param->result =
					utpm_pcrread(&utpmtest_param->pcr0, &utpmtest_param->utpm, utpmtest_param->pcr_num);

			return true;

	} else	if(uhcall_function == UAPP_UTPM_FUNCTION_EXTEND){
			//_XDPRINTFSMP_("%s: going to perform extend...pcr_num=%u\n",
			//		__func__, utpmtest_param->pcr_num);
			utpmtest_param->result =
					utpm_extend(&utpmtest_param->measurement,
							&utpmtest_param->utpm, utpmtest_param->pcr_num);

			//_XDPRINTFSMP_("%s: extend successful\n", __func__);

			return true;



	} else	if(uhcall_function == UAPP_UTPM_FUNCTION_SEAL){
		//_XDPRINTFSMP_("%s: SEAL function: seal_inbuf_len=%u\n", __func__,
			//	utpmtest_param->seal_inbuf_len);

			#if 1
				utpmtest_param->result =
						utpm_seal(&utpmtest_param->utpm, &utpmtest_param->tpmPcrInfo,
								&utpmtest_param->seal_inbuf, utpmtest_param->seal_inbuf_len,
								&utpmtest_param->seal_outbuf, &utpmtest_param->seal_outbuf_len);
			#endif

			//_XDPRINTFSMP_("%s: SEAL function done: seal_outbuf_len=%u\n", __func__,
			//		utpmtest_param->seal_outbuf_len);


			return true;

	} else	if(uhcall_function == UAPP_UTPM_FUNCTION_UNSEAL){
			//_XDPRINTFSMP_("%s: UNSEAL function: seal_outbuf_len=%u\n", __func__,
			//		utpmtest_param->seal_outbuf_len);

			#if 1
			//if(utpmtest_param->seal_outbuf_len <= 32){
				utpmtest_param->result =
						utpm_unseal(&utpmtest_param->utpm,
									 &utpmtest_param->seal_outbuf, utpmtest_param->seal_outbuf_len,
									 &utpmtest_param->seal_outbuf2, &utpmtest_param->seal_outbuf2_len,
									 &utpmtest_param->digestAtCreation);
			//}else
			//	utpmtest_param->result = UTPM_ERR;
			#endif

			//_XDPRINTFSMP_("%s: UNSEAL function done: seal_outbuf2_len=%u\n", __func__,
			//		utpmtest_param->seal_outbuf2_len);

			return true;


	}else{
		return false;
	}
}
