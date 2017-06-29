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

	if(uhcall_function == UAPP_UTPM_FUNCTION_INIT_MASTER_ENTROPY){
		utpmtest_param->result =
				utpm_init_master_entropy(&utpmtest_param->g_aeskey,
						&utpmtest_param->g_hmackey,
						&utpmtest_param->g_rsakey);

		return true;

	} else	if(uhcall_function == UAPP_UTPM_FUNCTION_INIT_INSTANCE){

			utpm_init_instance(&utpmtest_param->utpm);

			return true;

	}else{
		return false;
	}
}
