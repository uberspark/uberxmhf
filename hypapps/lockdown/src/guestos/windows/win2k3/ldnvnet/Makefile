# Makefile for cygwin environments to build the 
# lockdown birtual network adapter driver
# author: amit vasudevan (amitvasudevan@acm.org)

#external scripts
BUILD_SCRIPT = mksys.bat

export DRV_INSTALL_DIR := .
 

# targets
.PHONY: all
all: 
	/cygdrive/c/windows/system32/cmd.exe /c ".\mksys.bat"
	cp ./sys/objchk_wnet_x86/i386/ldnvnet.sys $(DRV_INSTALL_DIR)/ldnvnet.sys
	cp ./sys/objchk_wnet_x86/i386/ldnvnet.pdb $(DRV_INSTALL_DIR)/ldnvnet.pdb
	cp ./sys/ldnvnet.inf $(DRV_INSTALL_DIR)/ldnvnet.inf
	

.PHONY: clean 
clean: 
	$(RM) -rf ./sys/objchk_wnet_x86
	$(RM) -rf ./sys/*.log
	$(RM) -rf ./sys/*.err
	$(RM) -rf ./sys/*.wrn
	 
  

  
