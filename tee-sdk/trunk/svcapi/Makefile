include Makefile.inc

# test if we're on a vmx platform.
# FIXME this is brittle, and assumes that the target
# platform and the host platform are the same.
# best solution would be for compiled code to do a runtime check
# so that it will work on both vmx and non-vmx platforms
VMXTEST=$(shell egrep -q '^flags.*\bvmx\b' /proc/cpuinfo ; echo $$?)
ifeq (0, $(VMXTEST))
  IS_VMX=-DIS_VMX
  $(warning "is vmx")
else ifeq (1, $(VMXTEST))
  IS_VMX=
  $(warning "is not vmx")
else
  $(error "couldn't determine if platform is vmx")
endif

INCLUDES=-I../tz/dev/tv/include/
CFLAGS=$(IS_VMX) $(SVC_CFLAGS) -g $(INCLUDES)

OBJS=svcapi.o

all: libsvcapi.a

libsvcapi.a: $(OBJS)
	ar rcs $@ $<

clean:
	$(RM) libsvcapi.a $(OBJS)
