#-------------------------------------------------------------------------------
# top-level makefile for apps based on emhf
# author: amit vasudevan (amitvasudevan@acm.org)

# the build process goes like this:
# we first enter app and run the top-level makefile there
#   - this will create app objs in app/objects/*
# we then enter emhfcore and run the top-level makefile there
#   - this will create init and hypervisor binaries for the app
#			depending on the h/w platform (x86) selected
# we finally move the above two to the top-level directory where this
# makefile is located

#-----options that need tweaking w.r.t your development

    #your target name and version
    export TARGET = trustvisor
    export TARGET_VERSION = 0
    export TARGET_SUBVERSION = 1

    #h/w platform, current choices are x86
	export TARGET_HWPLATFORM := x86

    #MP/UP selection, y=Multiprocessor, n=Uniprocessor
    export MP_VERSION := y

    #where you want loader and runtime binaries to go, defaults to
    #current dir. Note that this is used by the emhfcore to decide
    #where to put the files that result from the build process.
    #A better name might be BUILDTARGETDIR or similar.
	export INSTALLDIR = $(CURDIR)

    #misc. configuaration w.r.t serial debugging and NPT/EPT support
	export NESTED_PAGING := y
    export DEBUG_SERIAL := y
    export DEBUG_SERIAL_PORT := 0x3f8
	export DEBUG_VGA	:= n

#-----configuration for subdirectories containing "library-able"
#-----functionality that TrustVisor uses, but that may also be
#-----useful elsewhere.

#-----configuration that typically need not be touched
# TODO: THESE SHOULD BE PASSED IN FROM THE CORE BUILD OR SET USING ./configure
  ifeq ($(TARGET_HWPLATFORM), x86)
  export EMHFROOTDIR := ../../../emhf/trunk/code
  export EMHFCOREDIR := $(EMHFROOTDIR)/x86
  endif

  export EMHFUTILDIR := $(EMHFROOTDIR)/libemhfutil
  export EMHFCDIR := $(EMHFROOTDIR)/libemhfc
  export EMHFCRYPTODIR := $(EMHFROOTDIR)/libemhfcrypto
  export TV_UTPMDIR := $(EMHFROOTDIR)/libtv_utpm

  export BASEDIR = /home/jmmccune/work/hyp.git/trustvisor/trunk/code
  export APPOBJECTSDIR = $(BASEDIR)/app/objects
  export EMHF_INCLUDEDIR = $(BASEDIR)/$(EMHFCOREDIR)/include
  export EMHFUTIL_INCLUDEDIR = $(BASEDIR)/$(EMHFUTILDIR)/include
  export EMHFC_INCLUDEDIR = $(BASEDIR)/$(EMHFCDIR)/include
  export EMHFCRYPTO_INCLUDEDIR = $(BASEDIR)/$(EMHFCRYPTODIR)/include
  export TV_UTPM_INCLUDEDIR = $(BASEDIR)/$(TV_UTPMDIR)/include
  export INCLUDEDIR = $(EMHF_INCLUDEDIR)
  export APP_INCLUDEDIR = $(BASEDIR)/app/include
  export EMHFAPP = y

  export prefix=/usr/local
  export exec_prefix=${prefix}
  export libdir=${exec_prefix}/lib
  export includedir=${prefix}/include
  export pkgconfigdir=${libdir}/pkgconfig
  export pkgincludedir=${includedir}/trustvisor

#-----tools
  export CC = gcc
  export AS = as
  export LD = ld
  export OBJDUMP = objdump
  export OBJCOPY = objcopy
  export STRIP = strip
  export O_CC = /bin/gcc
  export RM = rm -f
  export CP = cp
  export O_LD = /bin/ld
  export TAR = tar
  export SED = sed
  export MKDIR = mkdir
  export CAT = cat

#-----basic flags for compiling
  CFLAGS = -fno-builtin -fno-common -fno-strict-aliasing -iwithprefix include
  CFLAGS += -fno-stack-protector
  CFLAGS += -Wimplicit-function-declaration
  CFLAGS += -Wall
  CFLAGS += -Wparentheses
  CFLAGS += -Wunused
  CFLAGS += -Wstrict-prototypes -Wdeclaration-after-statement 
  CFLAGS += -Werror -Wno-pointer-arith -Wextra -Wfloat-equal 
  CFLAGS += -Wbad-function-cast -Wcast-qual -Wsign-compare 
  CFLAGS += -Waggregate-return
  CFLAGS += -Winline
  CFLAGS += -m32 -march=k8
  CFLAGS += -mno-sse2
  CFLAGS += -nostdinc -pipe -I$(EMHF_INCLUDEDIR) -I$(APP_INCLUDEDIR) -I$(EMHFUTIL_INCLUDEDIR) -I$(EMHFC_INCLUDEDIR) -I$(EMHFCRYPTO_INCLUDEDIR)
  CFLAGS += -I$(TV_UTPM_INCLUDEDIR)

#-----generate compiler/assembler defines from configuration options selected
  ifeq ($(NESTED_PAGING), y)
  CFLAGS += -D__NESTED_PAGING__
  endif
  ifeq ($(DEBUG_SERIAL), y)
  CFLAGS += -D__DEBUG_SERIAL__
  CFLAGS += -DDEBUG_PORT=$(DEBUG_SERIAL_PORT)
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

# default target: headers and binaries
install: install-dev install-bin

# install headers
install-dev:
	install -d $(DESTDIR)$(pkgconfigdir)
	install --mode=644 trustvisor.pc $(DESTDIR)$(pkgconfigdir)

	install -d $(DESTDIR)$(pkgincludedir)
	install app/include/trustvisor.h $(DESTDIR)$(pkgincludedir)

# install loader and runtime binaries to installation location
# TODO: make '/boot' configurable with ./configure
install-bin:
	install -d $(DESTDIR)/boot
	#install --mode=644 $(INSTALLDIR)/$(TARGET)-hypervisor-$(TARGET_HWPLATFORM).bin.gz $(DESTDIR)/boot
	#install --mode=644 $(INSTALLDIR)/$(TARGET)-init-$(TARGET_HWPLATFORM).bin $(DESTDIR)/boot
	# NOTE: Getting rid of TARGET prefix on hypervisor and init
	# because it will break the grub config on all of our test machines
	# right now.
	install --mode=644 $(INSTALLDIR)/$(TARGET)-hypervisor-$(TARGET_HWPLATFORM).bin.gz $(DESTDIR)/boot/hypervisor-$(TARGET_HWPLATFORM).bin.gz
	install --mode=644 $(INSTALLDIR)/$(TARGET)-init-$(TARGET_HWPLATFORM).bin $(DESTDIR)/boot/init-$(TARGET_HWPLATFORM).bin

#------test rules
test:
	cd test && $(MAKE) -w all

#------cleanup rules
.PHONY: clean distclean test
clean: 
	cd app && $(MAKE) -w clean
	rm -rf $(APPOBJECTSDIR) app_trustvisor.a
	cd test && $(MAKE) -w clean
	rm -f *.bin
	rm -f *.bin.gz

distclean:
	rm -f config.log
	rm -f config.status

#-----autoconf rules
Makefile: Makefile.in config.status
	./config.status $@

config.status: configure
	./config.status --recheck

configure: configure.ac
	./autogen.sh
