#-------------------------------------------------------------------------------
# Makefile for quiesce XMHF hypapp - guest OS control
# author: amit vasudevan (amitvasudevan@acm.org)

# target arch: valid values are x86svm and x86vmx
export TARGET_CPU = x86vmx

#-----generate compiler/assembler defines from configuration options selected
ifeq ($(TARGET_CPU), x86vmx)
CFLAGS += -D__X86VMX__
endif
ifeq ($(TARGET_CPU), x86svm)
CFLAGS += -D__X86SVM__
endif

.PHONY: all
all:
	gcc $(CFLAGS) qcontrol.c -o qcontrol
	
# cleanup
.PHONY: clean
clean: 
	rm -rf qcontrol

