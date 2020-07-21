#include <uberspark.h>
#include <xmhf-hwm.h>

#include <uapi_gcpustate.h>
#include <xh_ssteptrace.h>


{
	"uobj-name": "xh_ssteptrace",
	"uobj-type": "uVU_SLAB",
	"uobj-subtype": "XHYPAPP",

	"uobj-uapifunctions":[],

	"uobj-callees": " 	uapi_gcpustate
					",

	"uobj-uapicallees":[
		{ 
			"uobj-name": "uapi_gcpustate",
			"uobj-uapifunctionid": USMF_STR(XMHF_HIC_UAPI_CPUSTATE_VMREAD), 
			"opt1" : "(void)0;",
			"opt2" : "(1)" 
		},
		{ 
			"uobj-name": "uapi_gcpustate",
			"uobj-uapifunctionid": USMF_STR(XMHF_HIC_UAPI_CPUSTATE_VMWRITE), 
			"opt1" : "(void)0;",
			"opt2" : "(1)" 
		},
		{ 
			"uobj-name": "uapi_gcpustate",
			"uobj-uapifunctionid": USMF_STR(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSREAD), 
			"opt1" : "(void)0;",
			"opt2" : "(1)" 
		}
	],


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
			"section-size": "0x200000"
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








