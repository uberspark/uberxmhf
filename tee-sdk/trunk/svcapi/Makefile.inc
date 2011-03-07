#linker script to ensure proper layout, padding, etc.
LINK_SCRIPT = $(SVCAPIDIR)/svc.ld 

# prevent gcc from compiling switch statements as jump tables.
# can probably get rid of this in the future by somehow ensuring that
# the jump table data is also included in the svc memory areas
SVC_CFLAGS+=-fno-jump-tables

# Not sure whether this is necessary. Carried over from an old makefile
SVC_CFLAGS+=-fno-stack-protector

# include this directory. layout.h needs this.
SVC_CFLAGS+=-I $(SVCAPIDIR)

# use the designated linker script
SVC_LDFLAGS+= -T $(LINK_SCRIPT)
