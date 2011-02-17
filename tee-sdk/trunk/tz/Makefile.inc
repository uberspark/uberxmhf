CC=gcc
LD=ld
RM=rm -f

# config options. enable\disable these
#IS_WINDOWS=-DIS_WINDOWS
IS_WINDOWS=
IS_VMX=-DIS_VMX
#IS_VMX=

CFLAGS=-g $(IS_WINDOWS) $(IS_VMX) -DnotPERFCPIT -fno-stack-protector -Wall -I$(REL)/include
