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
	if(uhcall_function == UAPP_UTPM_FUNCTION_INIT_MASTER_ENTROPY){
		utpm_init_master_entropy_param_t *utpm_init_master_entropy_param =
				(utpm_init_master_entropy_param_t *)uhcall_buffer;

		utpm_init_master_entropy_param->result =
				utpm_init_master_entropy(&utpm_init_master_entropy_param->g_aeskey,
						&utpm_init_master_entropy_param->g_hmackey,
						&utpm_init_master_entropy_param->g_rsakey);

		return true;

	}else{
		return false;
	}
}
