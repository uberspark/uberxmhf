# top-level makefile for emhf AMD MP platform 
# author: amit vasudevan (amitvasudevan@acm.org)


#-----configuration, only needed to test this branch without emhfapp
	#-----options that need tweaking w.r.t your development
	  
		#your target name and version
		export TARGET = emhfapp
	  export TARGET_VERSION = 0
	  export TARGET_SUBVERSION = 1
	  #h/w platform, current choices are svm (for AMD) and vmx (for Intel)
		export TARGET_HWPLATFORM := svm
		#MP/UP selection, y=Multiprocessor, n=Uniprocessor
	  export MP_VERSION := y
		#where you want loader and runtime binaries to go, defaults to current dir.
		#export INSTALLDIR = $(CURDIR)
		export INSTALLDIR = /cygdrive/x/
	  #misc. configuaration w.r.t serial debugging and NPT/EPT support
		export NESTED_PAGING := y
	  export DEBUG_SERIAL := y
	  export DEBUG_VGA	:= n
	
	#-----configuration that typically need not be touched
	  ifeq ($(TARGET_HWPLATFORM), svm)
	  export EMHFCOREDIR := .
	  endif
	  ifeq ($(TARGET_HWPLATFORM), vmx)
	  export EMHFCOREDIR := .
		endif
	
	  export BASEDIR = $(CURDIR)
	  export APPOBJECTSDIR = $(BASEDIR)/app/objects
	  export EMHF_INCLUDEDIR = $(BASEDIR)/$(EMHFCOREDIR)/include
	  export INCLUDEDIR = $(EMHF_INCLUDEDIR)
	  export APP_INCLUDEDIR = $(BASEDIR)/app/include
	  export EMHFAPP = y
	
	#-----tools
	  export CC = gcc
	  export AS = as
	  export LD = ld
	  export OBJDUMP = objdump
	  export OBJCOPY = objcopy
	  export STRIP = strip
	  export O_CC = /bin/gcc
	  export RM = rm 
	  export CP = cp
	  export CAT = cat
	  export O_LD = /bin/ld
	  export TAR = tar
	  export SED = sed
	  export MKDIR = mkdir
	  
	
	#-----basic flags for compiling
	  CFLAGS = -fno-builtin -fno-common -fno-strict-aliasing -iwithprefix include
	  CFLAGS += -fno-stack-protector
	  CFLAGS += -Wstrict-prototypes -Wdeclaration-after-statement 
	  CFLAGS += -Werror -Wno-pointer-arith -Wextra -Wfloat-equal 
	  CFLAGS += -Wbad-function-cast -Wcast-qual -Wsign-compare 
	  CFLAGS += -Waggregate-return
	  CFLAGS += -Winline
	  CFLAGS += -m32 -march=k8 
	  CFLAGS += -nostdinc -pipe -I$(EMHF_INCLUDEDIR) -I$(APP_INCLUDEDIR)
	
	#-----generate compiler/assembler defines from configuration options selected
	  ifeq ($(NESTED_PAGING), y)
	  CFLAGS += -D__NESTED_PAGING__
	  endif
	  ifeq ($(DEBUG_SERIAL), y)
	  CFLAGS += -D__DEBUG_SERIAL__
	  endif
	  ifeq ($(DEBUG_VGA), y)
	  CFLAGS += -D__DEBUG_VGA__
	  endif
	  ifeq ($(MP_VERSION), y)
	  CFLAGS += -D__MP_VERSION__
	  endif
	
	
	  ASFLAGS = $(CFLAGS) -D__ASSEMBLY__
	
	  export CFLAGS
	  export ASFLAGS


#-----build rules
.PHONY: all
all: 
  
	#make libcommon first	
	cd libcommon && $(MAKE) -w all

	#make init	
	cd init && $(MAKE) -w all

	#make sl
	cd sl && $(MAKE) -w all

	#make runtime
	cd runtime && $(MAKE) -w all
	#cd runtime && gzip -c runtime.bin > runtime.bin.gz


 	# copy the init image to installation location
	$(CP) $(EMHFCOREDIR)/init/init.bin $(INSTALLDIR)/init-$(TARGET_HWPLATFORM).bin
	
	
	# concatenate 64K sl image and runtime image and copy to installation loc.
	$(CAT) $(EMHFCOREDIR)/sl/sl.bin $(EMHFCOREDIR)/runtime/runtime.bin > $(EMHFCOREDIR)/hypervisor.tmp.img
	$(CP) $(EMHFCOREDIR)/hypervisor.tmp.img $(INSTALLDIR)/hypervisor-$(TARGET_HWPLATFORM).bin
	#$(RM) -rf $(EMHFCOREDIR)/hypervisor.tmp.img 

# cleanup rules
.PHONY: clean 
clean: 
	cd runtime && $(MAKE) -w clean
	cd sl && $(MAKE) -w clean
	cd init && $(MAKE) -w clean
	cd libcommon && $(MAKE) -w clean
	
