#
# verify hypapp guest OS application makefile
#
# author: amit vasudevan (amitvasudevan@acm.org)
#

C_SOURCES = verifygos.c

I_SOURCES =  $(wildcard *.h)

OBJECTS = $(patsubst %.c, %.o, $(C_SOURCES))

TARGET = verifygos

LIBDIR := $(shell gcc -m32 -print-file-name=)


# target arch: valid values are x86svm and x86vmx
export TARGET_CPU = x86vmx

#-----generate compiler/assembler defines from configuration options selected
ifeq ($(TARGET_CPU), x86vmx)
CFLAGS += -D__X86VMX__
endif
ifeq ($(TARGET_CPU), x86svm)
CFLAGS += -D__X86SVM__
endif


# targets
.PHONY: all
all: $(OBJECTS) 
	gcc -m32 $(CFLAGS) -o $(TARGET) *.o -static

%.o: %.c $(I_SOURCES) Makefile 
	gcc -m32 -c $(CFLAGS) -o $@ $<

.PHONY: clean 
clean: 
	$(RM) -f *.o
	$(RM) -f $(TARGET)
 
  
  

  

