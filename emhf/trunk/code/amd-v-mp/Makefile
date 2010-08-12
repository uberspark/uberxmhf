# top-level makefile for emhf core 
# author: amit vasudevan (amitvasudevan@acm.org)

export MP_VERSION := y

  ifeq ($(MP_VERSION), y)
  CFLAGS += -D__MP_VERSION__
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


