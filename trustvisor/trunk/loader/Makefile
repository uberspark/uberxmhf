# Top-level makefile for Loader
# Created by Arvind Seshadri 3/30/07
# This file is set up so that all object files and the final executable 
# are placed in a separate directory than the sources (variable B_DIR 
# below). This is done so that source directories can be NFS mounted 
# read-only on testing machines. This should eliminate any chances of
# source file corruption if the testing machine were to become unstable.

# Make variables
# Recursively expanded variables are expanded at time of substitution.
# They are defined using = 
# Simply expanded variables are expanded at the time of definition.
# They are defined using :=
# $@ is the name of the target.          
# $< is the first prerequisite of the target.
# $^ is the list of all prerequisites.

export BASEDIR = $(CURDIR)
# Build directory
export B_DIR = loader_out

# Debug option 
# Change this to ECM50, POSSUM, or GDB, depending on whether you are using
# ECM50, POSSUM, or SimNow/GDB for debugging. Leave it empty if you don't 
# want debugging support

# Target name and version
export TARGET = TLoader

#verbosity                                                                     
#ifeq ($(V), 1)                                                           
#export VERBOSE=@
#endif

# Tools
export CC = gcc
export RM = rm 
export AS = as
export LD = ld
export MKELF = $(BASEDIR)/$(B_DIR)/mkelf32
export TAR = tar
export NM = nm
export OBJDUMP = objdump
export SED = sed

# Header files
export INCLUDE_DIR = -I$(BASEDIR)/include 

# Linker script
export LINKER_SCRIPT = $(BASEDIR)/$(B_DIR)/loader.lds

# Source files recompilation indicator
export COMPILE_H = $(BASEDIR)/$(B_DIR)/compile.h

# Source directories. If you add new source directories, add their
# names to this list.
export S_DIRS = boot
S_DIRS_CLEAN = $(patsubst %, %_clean, $(S_DIRS))

# rules for building the subdirectories
.PHONY: $(TARGET)
$(TARGET): $(BASEDIR)/$(B_DIR)
	$(MAKE) -C boot $(BASEDIR)/$(B_DIR)/$(TARGET).gz                     
$(BASEDIR)/$(B_DIR):
	cd $(BASEDIR);\
	mkdir $(B_DIR)

# rules for make clean. 
.PHONY: clean $(S_DIRS_CLEAN)
clean: $(S_DIRS_CLEAN)
	$(RM) -rf $(B_DIR)
	$(RM) -f *~
$(S_DIRS_CLEAN):
	$(MAKE) -C $(patsubst %_clean, %, $@) clean

#.PHONY: tar
#tar:
#	cd ..;\
#	$(TAR) cvfz loader.tar.gz --exclude .svn code/;\
#	scp -r loader.tar.gz swatt@penguin.ece.cmu.edu:Documents/.;\
#	ssh swatt@penguin 'cd Documents;tar xvfz loader.tar.gz;rm -f loader.tar.gz;rm -rf loader/;mv code loader';\
#	rm -f loader.tar.gz

.PHONY: install boot_install visor_install
install: boot_install visor_install
	cp $(BASEDIR)/$(B_DIR)/Loader.gz /boot

.PHONY: tags
tags:
	/usr/bin/ctags -e -R
