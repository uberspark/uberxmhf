/*
	pa5encfs hypapp
	FUSE encrypted filesystem hypapp

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

#include <pa5encfs.h>


//return true if handled the hypercall, false if not
bool uapp_pa5encfs_handlehcall(u32 uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len){
	pa5encfs_param_t *ep;

	ep = (pa5encfs_param_t *)uhcall_buffer;

	if(uhcall_function == UAPP_PA5ENCFS_FUNCTION_START){

		return true;

	}else if (uhcall_function == UAPP_PA5ENCFS_FUNCTION_ENCRYPT){


		return true;

	}else if (uhcall_function == UAPP_PA5ENCFS_FUNCTION_DECRYPT){


		return true;

	}else if (uhcall_function == UAPP_PA5ENCFS_FUNCTION_DONE){


		return true;
	}else{

		return false;
	}

}
