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

#include <uhcalltest.h>

uint32_t va2pa(uint32_t va){
	u32 ttbcr;

	_XDPRINTFSMP_("%s: ENTER: va=0x%08x\n", __func__, va);

	ttbcr = sysreg_read_ttbcr();
	_XDPRINTFSMP_("%s: ttbcr=0x%08x\n", __func__, ttbcr);

	_XDPRINTFSMP_("%s: WiP\n", __func__);
}

//return true if handled the hypercall, false if not
bool uapp_uhcalltest_handlehcall(u32 uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len){
	uhcalltest_param_t *uhctp;
	uint32_t i;

	if(uhcall_function != UAPP_UHCALLTEST_FUNCTION_TEST)
		return false;

	_XDPRINTFSMP_("%s: hcall: uhcall_function=0x%08x, uhcall_buffer=0x%08x, uhcall_buffer_len=0x%08x\n", __func__,
			uhcall_function, uhcall_buffer, uhcall_buffer_len);

	va2pa((uint32_t)uhcall_buffer);

#if 0
	uhctp = (uhcalltest_param_t *)uhcall_buffer;
   _XDPRINTFSMP_("dumping uhctp->in[]...\n");
   for(i=0; i < 16; i++)
	   _XDPRINTFSMP_("%c", uhctp->in[i]);
   _XDPRINTFSMP_("\ndumped uhctp->in[]\n");

   memcpy(&uhctp->out, &uhctp->in, 16);

   _XDPRINTFSMP_("dumping uhctp->out[]...\n");
   for(i=0; i < 16; i++)
	   _XDPRINTFSMP_("%c", uhctp->out[i]);
   _XDPRINTFSMP_("\ndumped uhctp->out[]\n");
#endif

	return true;
}
