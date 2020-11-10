{
 "uobj-name": "geec_prime",
 "uobj-type": "VfT_SLAB",
 "uobj-subtype": "PRIME",
 "uobj-uapifunctions":[],
 "uobj-callees": " 	geec_sentinel
      uapi_slabmempgtbl
      xc_init
      uapi_sysdata
      xc_ihub
      xc_exhub
     ",
 "uobj-uapicallees":[
  {
   "uobj-name": "uapi_slabmempgtbl",
   "uobj-uapifunctionid": "1",
   "opt1" : "(void)0;",
   "opt2" : "(1)"
  },
  {
   "uobj-name": "uapi_slabmempgtbl",
   "uobj-uapifunctionid": "0",
   "opt1" : "(void)0;",
   "opt2" : "(1)"
  },
  {
   "uobj-name": "uapi_sysdata",
   "uobj-uapifunctionid": "1",
   "opt1" : "(void)0;",
   "opt2" : "(1)"
  }
 ],
 "uobj-resource-devices":[
  {
   "type": "include",
   "opt1" : "0xFFFF",
   "opt2" : "0x0000"
  },
  {
   "type": "include",
   "opt1" : "0xFFFF",
   "opt2" : "0x0002"
  },
  {
   "type": "include",
   "opt1" : "0xFFFF",
   "opt2" : "0x0001"
  },
  {
   "type": "include",
   "opt1" : "0xFFFF",
   "opt2" : "0x0003"
  }
 ],
 "uobj-resource-memory":[],
 "uobj-exportfunctions": "",
 "uobj-binary-sections":[
  {
   "section-name": "code",
   "section-size": "0x200000"
  },
  {
   "section-name": "data",
   "section-size": "0x3800000"
  },
  {
   "section-name": "stack",
   "section-size": "0xe00000"
  },
  {
   "section-name": "dmadata",
   "section-size": "0x200000"
  }
 ],
 "c-files": "",
 "v-harness": []
}
