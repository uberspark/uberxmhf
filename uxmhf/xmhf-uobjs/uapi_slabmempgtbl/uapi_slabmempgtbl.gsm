#include <uberspark.h>
#include <xmhf-hwm.h>
#include <geec_sentinel.h>
#include <uapi_slabmempgtbl.h>

{
	"uobj-name": "uapi_slabmempgtbl",
	"uobj-type": "VfT_SLAB",
	"uobj-subtype": "UAPI",

	"uobj-uapifunctions":[
		{ 
			"uapifunction-id": USMF_STR(XMHFGEEC_UAPI_SLABMEMPGTBL_INITMEMPGTBL),
			"uapifunction-definition" : 
				"void _slabmempgtbl_initmempgtbl(xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t *initmempgtblp)", 
			"uapifunction-drivercode" : 
				"{xmhfgeec_uapi_slabmempgtbl_initmempgtbl_params_t initmempgtblp; initmempgtblp.dst_slabid = framac_nondetu32(); _slabmempgtbl_initmempgtbl(&initmempgtblp);}"
		},
		{ 
			"uapifunction-id": USMF_STR(XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR),
			"uapifunction-definition" : "void _slabmempgtbl_setentryforpaddr(xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t *setentryforpaddrp)", 
			"uapifunction-drivercode" : "{xmhfgeec_uapi_slabmempgtbl_setentryforpaddr_params_t setentryforpaddrp; setentryforpaddrp.dst_slabid = framac_nondetu32(); setentryforpaddrp.gpa = framac_nondetu32(); setentryforpaddrp.entry = framac_nondetu32(); _slabmempgtbl_setentryforpaddr(&setentryforpaddrp);}"
		},
		{ 
			"uapifunction-id": USMF_STR(XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR),
			"uapifunction-definition" : "void _slabmempgtbl_getentryforpaddr(xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t *getentryforpaddrp)", 
			"uapifunction-drivercode" : "{xmhfgeec_uapi_slabmempgtbl_getentryforpaddr_params_t getentryforpaddrp; getentryforpaddrp.dst_slabid = framac_nondetu32(); getentryforpaddrp.gpa = framac_nondetu32(); _slabmempgtbl_getentryforpaddr(&getentryforpaddrp);}"
		}
	],

	"uobj-callees": "	geec_sentinel
					",

	"uobj-uapicallees":[],


	"uobj-resource-devices":[],

	"uobj-resource-memory":[],	

	"uobj-exportfunctions": "",


	"uobj-binary-sections":[
		{ 
			"section-name": "code",
			"section-size": "0x200000"
		},
		{ 
			"section-name": "data",
			"section-size": "0x4200000"
		},
		{ 
			"section-name": "stack",
			"section-size": "0x600000"
		},
		{ 
			"section-name": "dmadata",
			"section-size": "0x200000"
		}
	],	

	
	"c-files":	"",
		
	"v-harness": []
		
	
}



