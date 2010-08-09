# top-level makefile for emhf core 
# author: amit vasudevan (amitvasudevan@acm.org)

#-------------------------------------------------------------------------------
ifeq ($(EMHFAPP), y)
# configuration options, tools, basic flags should all be set in the
# top-level makefile for the specific app

else

#-----configuration options
  export TARGET = target
  export TARGET_VERSION = 0
  export TARGET_SUBVERSION = 1
  export BASEDIR = $(CURDIR)
  export APPOBJECTSDIR = $(BASEDIR)/app/objects
  export EMHF_INCLUDEDIR = $(BASEDIR)/emhfcore/include
  export INCLUDEDIR = $(BASEDIR)/include
  export APP_INCLUDEDIR = $(BASEDIR)/app/include
  export INSTALLDIR = $(CURDIR)
  #export INSTALLDIR = /cygdrive/X
  
  export MP_VERSION := y
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
  CFLAGS += -nostdinc -pipe -I$(INCLUDEDIR)
  
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
#-------------------------------------------------------------------------------

endif

#-----build rules
.PHONY: all
all: 
  
	#make common and debug components first	
	cd common && $(MAKE) -w all
	cd debug && $(MAKE) -w all

	#make loader	
	cd loader && $(MAKE) -w all

	#make runtime
	cd runtime	&& $(MAKE) -w all
	cd runtime && gzip -c runtime.bin > runtime.bin.gz

# cleanup rules
.PHONY: clean 
clean: 
	cd common && $(MAKE) -w clean
	cd debug && $(MAKE) -w clean
	cd loader && $(MAKE) -w clean
	cd runtime && $(MAKE) -w clean


