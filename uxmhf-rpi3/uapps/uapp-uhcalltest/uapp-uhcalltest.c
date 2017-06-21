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

#define UAPP_UHCALLTEST_FUNCTION_TEST	10

//return true if handled the hypercall, false if not
bool uapp_uhcalltest_handlehcall(u32 uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len){
	if(uhcall_function != UAPP_UHCALLTEST_FUNCTION_TEST)
		return false;

	_XDPRINTFSMP_("%s: hcall: uhcall_function=0x%08x, uhcall_buffer=0x%08x, uhcall_buffer_len=0x%08x\n", __func__,
			uhcall_function, uhcall_buffer, uhcall_buffer_len);

	return true;
}
