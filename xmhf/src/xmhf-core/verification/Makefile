# makefile for XMHF core verification
# author: amit vasudevan (amitvasudevan@acm.org)

# source files
AS_SOURCES =  

.PHONY: verify 
verify: 
	cbmc $(VFLAGS) -D__XMHF_VERIFICATION__ --bounds-check --pointer-check xmhf-core-vdriver.c 
	
  

  
