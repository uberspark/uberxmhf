#-------------------------------------------------------------------------------
# top-level makefile for apps based on emhf
# author: amit vasudevan (amitvasudevan@acm.org)

# the build process goes like this:
# we first enter app and run the top-level makefile there
#   - this will create app objs in app/objects/*
# we then enter emhfcore and run the top-level makefile there
#   - this will create loader.bin, runtime.bin.gz for the app
#			depending on the h/w platform (AMD SVM vs Intel VMX) selected
# we finally move the above two to the top-level directory where this
# makefile is located

#-----options that need tweaking w.r.t your development
  
	#your target name and version
	export TARGET = lockdown
  export TARGET_VERSION = 0
  export TARGET_SUBVERSION = 3
  #h/w platform, current choices are svm (for AMD) and vmx (for Intel)
	export TARGET_HWPLATFORM := vmx
	#MP/UP selection, y=Multiprocessor, n=Uniprocessor
  export MP_VERSION := n
	#where you want loader and runtime binaries to go, defaults to current dir.
	#export INSTALLDIR = $(CURDIR)
	export INSTALLDIR = /cygdrive/z/
  #misc. configuaration w.r.t serial debugging and NPT/EPT support
	export NESTED_PAGING := y
  export DEBUG_SERIAL := y
  export DEBUG_VGA	:= n

#-----configuration that typically need not be touched
  ifeq ($(TARGET_HWPLATFORM), svm)
  export EMHFCOREDIR := ./emhfcore/amd-v-mp
  endif
  ifeq ($(TARGET_HWPLATFORM), vmx)
  export EMHFCOREDIR := ./emhfcore/intel-vt-mp
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
  # CFLAGS += -O2

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
  # make app components
	mkdir -p $(APPOBJECTSDIR)
	cd app && $(MAKE) -w all
  
	# make emhf core components and generate loader and runtime	
	cd $(EMHFCOREDIR) && $(MAKE) -w all

	# copy the app loader and runtime binaries to installation location
	$(CP) $(EMHFCOREDIR)/loader/loader.bin $(INSTALLDIR)/$(TARGET)-loader-$(TARGET_HWPLATFORM).bin
	$(CP) $(EMHFCOREDIR)/runtime/runtime.bin.gz $(INSTALLDIR)/$(TARGET)-runtime-$(TARGET_HWPLATFORM).bin.gz
	
#------cleanup rules
.PHONY: clean 
clean: 
	cd app && $(MAKE) -w clean
	rm -rf $(APPOBJECTSDIR)
	cd $(EMHFCOREDIR) && $(MAKE) -w clean

