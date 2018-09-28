#include <uberspark.h>
#include <xmhf-hwm.h>

#include <uapi_gcpustate.h>
#include <uapi_slabmempgtbl.h>
#include <xh_syscalllog.h>
#include <xc_nwlog.h>

{
	"uobj-name": "xh_syscalllog",
	"uobj-type": "VfT_SLAB",
	"uobj-subtype": "XHYPAPP",

	"uobj-uapifunctions":[],


	"uobj-callees": " 	uapi_gcpustate
						uapi_slabmempgtbl
						xc_nwlog
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
		},
		{ 
			"uobj-name": "uapi_gcpustate",
			"uobj-uapifunctionid": USMF_STR(XMHF_HIC_UAPI_CPUSTATE_GUESTGPRSWRITE), 
			"opt1" : "(void)0;",
			"opt2" : "(1)" 
		},
		{ 
			"uobj-name": "uapi_slabmempgtbl",
			"uobj-uapifunctionid": USMF_STR(XMHFGEEC_UAPI_SLABMEMPGTBL_GETENTRYFORPADDR), 
			"opt1" : "(void)0;",
			"opt2" : "(1)" 
		},
		{ 
			"uobj-name": "uapi_slabmempgtbl",
			"uobj-uapifunctionid": USMF_STR(XMHFGEEC_UAPI_SLABMEMPGTBL_SETENTRYFORPADDR), 
			"opt1" : "if (setentryforpaddrp->gpa == 0){setentryforpaddrp->entry = setentryforpaddrp->entry & 7; setentryforpaddrp->entry &= ~(0x4); setentryforpaddrp->entry |=0x1; setentryforpaddrp->entry |= 0x2;}",
			"opt2" : "((setentryforpaddrp->gpa != 0) || (setentryforpaddrp->gpa==0 && !(setentryforpaddrp->entry & 0x4) && (setentryforpaddrp->entry & 0x1) && (setentryforpaddrp->entry & 0x2)))" 
		},
		{ 
			"uobj-name": "uapi_slabmempgtbl",
			"uobj-uapifunctionid": USMF_STR(XMHFGEEC_UAPI_SLABMEMPGTBL_FLUSHTLB), 
			"opt1" : "(void)0;",
			"opt2" : "(1)" 
		},
		{ 
			"uobj-name": "xc_nwlog",
			"uobj-uapifunctionid": USMF_STR(XMHFGEEC_SLAB_XC_NWLOG_INITIALIZE), 
			"opt1" : "(void)0;",
			"opt2" : "(1)" 
		},
		{ 
			"uobj-name": "xc_nwlog",
			"uobj-uapifunctionid": USMF_STR(XMHFGEEC_SLAB_XC_NWLOG_LOGDATA), 
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















