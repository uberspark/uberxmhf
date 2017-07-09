/*
	uhcalltest hypapp
	guest hypercall test hypapp

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

#include <xmhfcrypto.h>
#include <utpm.h>
#include <utpmtest.h>


//return true if handled the hypercall, false if not
bool uapp_utpmtest_handlehcall(u32 uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len){
	utpmtest_param_t *utpmtest_param = 	(utpmtest_param_t *)uhcall_buffer;

	_XDPRINTFSMP_("%s: uhcall_function=%x, uhcall_buffer=0x%08x, uhcall_buffer_len=%u\n",
			__func__, uhcall_function, uhcall_buffer, uhcall_buffer_len);

	if(uhcall_function == UAPP_UTPM_FUNCTION_INIT_MASTER_ENTROPY){
		utpmtest_param->result =
				utpm_init_master_entropy(&utpmtest_param->g_aeskey,
						&utpmtest_param->g_hmackey,
						&utpmtest_param->g_rsakey);

		return true;

	} else	if(uhcall_function == UAPP_UTPM_FUNCTION_INIT_INSTANCE){

			utpm_init_instance(&utpmtest_param->utpm);

			return true;

	} else	if(uhcall_function == UAPP_UTPM_FUNCTION_PCRREAD){

			utpmtest_param->result =
					utpm_pcrread(&utpmtest_param->pcr0, &utpmtest_param->utpm, &utpmtest_param->pcr_num);

			return true;

	} else	if(uhcall_function == UAPP_UTPM_FUNCTION_EXTEND){
			utpmtest_param->result =
					utpm_extend(&utpmtest_param->measurement,
							&utpmtest_param->utpm, utpmtest_param->pcr_num);

			return true;



	} else	if(uhcall_function == UAPP_UTPM_FUNCTION_SEAL){
		_XDPRINTFSMP_("%s: SEAL function: seal_inbuf_len=%u\n", __func__,
				utpmtest_param->seal_inbuf_len);

			#if 0
			utpmtest_param->result =
					utpm_seal(&utpmtest_param->utpm, &utpmtest_param->tpmPcrInfo,
							&utpmtest_param->seal_inbuf, utpmtest_param->seal_inbuf_len,
							&utpmtest_param->seal_outbuf, &utpmtest_param->seal_outbuf_len);
			#else

			utpmtest_param->result = UTPM_SUCCESS;
			#endif

			_XDPRINTFSMP_("%s: SEAL function done: seal_outbuf_len=%u\n", __func__,
					utpmtest_param->seal_outbuf_len);


			return true;

	} else	if(uhcall_function == UAPP_UTPM_FUNCTION_UNSEAL){
			_XDPRINTFSMP_("%s: UNSEAL function: seal_outbuf_len=%u\n", __func__,
					utpmtest_param->seal_outbuf_len);

			#if 0
			utpmtest_param->result =
					utpm_unseal(&utpmtest_param->utpm,
					             &utpmtest_param->seal_outbuf, utpmtest_param->seal_outbuf_len,
					             &utpmtest_param->seal_outbuf2, &utpmtest_param->seal_outbuf2_len,
					             &utpmtest_param->digestAtCreation);
			#else
			utpmtest_param->result = UTPM_SUCCESS;
			#endif

			_XDPRINTFSMP_("%s: UNSEAL function done: seal_outbuf2_len=%u\n", __func__,
					utpmtest_param->seal_outbuf2_len);

			return true;


	}else{
		return false;
	}
}
