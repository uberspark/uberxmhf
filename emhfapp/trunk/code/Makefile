#-------------------------------------------------------------------------------
# top-level makefile for apps based on emhf
# author: amit vasudevan (amitvasudevan@acm.org)

# the build process goes like this:
# we first enter app and run the top-level makefile there
#   - this will create app objs in app/objects/*
# we then enter emhfcore and run the top-level makefile there
#   - this will create loader.bin, runtime.bin.gz for the app
# we finally move the above two to the top-level directory where this
# makefile is located

#-----configuration options
  export TARGET = target
  export TARGET_VERSION = 0
  export TARGET_SUBVERSION = 1
  export BASEDIR = $(CURDIR)
  export APPOBJECTSDIR = $(BASEDIR)/app/objects
  export EMHF_INCLUDEDIR = $(BASEDIR)/emhfcore/include
  export INCLUDEDIR = $(EMHF_INCLUDEDIR)
  export APP_INCLUDEDIR = $(BASEDIR)/app/include
  export INSTALLDIR = $(CURDIR)
  export EMHFAPP = y

  export NESTED_PAGING := y
  export DEBUG_SERIAL := y
  export DEBUG_VGA	:= n

#-----tools
  # change the line below to where you have the tools installed
  export TOOLSBASE = /cygdrive/c/amit/tools/bin
  export CC = $(TOOLSBASE)/gcc
  export O_CC = /bin/gcc
  export RM = rm 
  export CP = cp
  export AS = $(TOOLSBASE)/as
  export LD = $(TOOLSBASE)/ld
  export O_LD = /bin/ld
  export TAR = tar
  export OBJDUMP = $(TOOLSBASE)/objdump
  export OBJCOPY = $(TOOLSBASE)/objcopy
  export SED = sed
  export STRIP = $(TOOLSBASE)/strip
  export MKDIR = mkdir
  

#-----basic flags for compiling
  CFLAGS = -fno-builtin -fno-common -fno-strict-aliasing -iwithprefix include
  CFLAGS += -fno-stack-protector
  CFLAGS += -Wstrict-prototypes -Wdeclaration-after-statement 
  CFLAGS += -Werror -Wno-pointer-arith -Wextra -Wfloat-equal 
  CFLAGS += -Wbad-function-cast -Wcast-qual -Wsign-compare 
  CFLAGS += -Waggregate-return
  CFLAGS += -Wunreachable-code -Winline
  CFLAGS += -m32 -march=k8 
  CFLAGS += -nostdinc -pipe -I$(SECHYP_INCLUDEDIR) -I$(APP_INCLUDEDIR)

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
	cd emhfcore && $(MAKE) -w all

	# copy the app loader and runtime binaries to installation location
	$(CP) ./emhfcore/loader/loader.bin $(INSTALLDIR)/loader.bin
	$(CP) ./emhfcore/runtime/runtime.bin.gz $(INSTALLDIR)/runtime.bin.gz
	
#------cleanup rules
.PHONY: clean 
clean: 
	cd app && $(MAKE) -w clean
	rm -rf $(APPOBJECTSDIR)
	cd emhfcore && $(MAKE) -w clean

