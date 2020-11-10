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
   "uobj-uapifunctionid": "0",
   "opt1" : "(void)0;",
   "opt2" : "(1)"
  },
  {
   "uobj-name": "uapi_gcpustate",
   "uobj-uapifunctionid": "1",
   "opt1" : "(void)0;",
   "opt2" : "(1)"
  },
  {
   "uobj-name": "uapi_gcpustate",
   "uobj-uapifunctionid": "2",
   "opt1" : "(void)0;",
   "opt2" : "(1)"
  },
  {
   "uobj-name": "uapi_gcpustate",
   "uobj-uapifunctionid": "3",
   "opt1" : "(void)0;",
   "opt2" : "(1)"
  },
  {
   "uobj-name": "uapi_slabmempgtbl",
   "uobj-uapifunctionid": "2",
   "opt1" : "(void)0;",
   "opt2" : "(1)"
  },
  {
   "uobj-name": "uapi_slabmempgtbl",
   "uobj-uapifunctionid": "1",
   "opt1" : "if (setentryforpaddrp->gpa == 0){setentryforpaddrp->entry = setentryforpaddrp->entry & 7; setentryforpaddrp->entry &= ~(0x4); setentryforpaddrp->entry |=0x1; setentryforpaddrp->entry |= 0x2;}",
   "opt2" : "((setentryforpaddrp->gpa != 0) || (setentryforpaddrp->gpa==0 && !(setentryforpaddrp->entry & 0x4) && (setentryforpaddrp->entry & 0x1) && (setentryforpaddrp->entry & 0x2)))"
  },
  {
   "uobj-name": "uapi_slabmempgtbl",
   "uobj-uapifunctionid": "3",
   "opt1" : "(void)0;",
   "opt2" : "(1)"
  },
  {
   "uobj-name": "xc_nwlog",
   "uobj-uapifunctionid": "0",
   "opt1" : "(void)0;",
   "opt2" : "(1)"
  },
  {
   "uobj-name": "xc_nwlog",
   "uobj-uapifunctionid": "1",
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
 "c-files": "",
 "v-harness": []
}
