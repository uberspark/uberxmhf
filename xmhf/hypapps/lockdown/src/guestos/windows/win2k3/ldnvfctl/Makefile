# ldnvfctl makefile
# author: amit vasudevan (amitvasudevan@acm.org)

!IF "$(TARGETOS)" == "WINNT"

!include <Win32.Mak>

OUTDIR = .
LDNVFCTL_INSTALLDIR = c:\ldnvfctl
SSLPA_ROOT= $(OUTDIR)\sslpa

########################################################################
# external dependencies
########################################################################
# Windows PCAP developers pack and sources (BSD)
WINPCAP_DEV_DIR=c:\WPdpack
WINPCAP_SRC_DIR=c:\winpcap
WINPCAP_LIB_DIR=$(WINPCAP_DEV_DIR)\lib
# Libusb (LGPLv2.1)
LIBUSB_WIN32_DIR=c:\libusb-win32-device-bin-0.1.12.1
########################################################################


# include dependencies
SSLPA_INCLUDES = -I$(SSLPA_ROOT)\base \
	-I$(SSLPA_ROOT)\common\include \
	-I$(SSLPA_ROOT)\common\lib \
	-I$(SSLPA_ROOT)\null \
	-I$(SSLPA_ROOT)\ssl \
	-I$(SSLPA_ROOT)\win32 \
	-I$(WINPCAP_DEV_DIR)\include \
	-I$(WINPCAP_DEV_DIR)\include\net \
	-I$(WINPCAP_SRC_DIR)\wpcap\libpcap\win32\include	

# lib dependencies
SSLPA_LIBS = gdi32.lib \
	Wsock32.lib \
	kernel32.lib \
	$(WINPCAP_LIB_DIR)\lib\wpcap.lib

# defines needed
SSLPA_DEFINES=/D STDC /D WIN32 /D _CONSOLE \
	$(OPENSSL_DEFINES) /D STDC_HEADERS /D SIZEOF_UNSIGNED_SHORT=2 /D SIZEOF_UNSIGNED_LONG=4 \
	/D RETSIGTYPE=void /D SIZEOF_CHAR=1 /D SIZEOF_SHORT=2 /D SIZEOF_INT=4

# cflags needed
SSLPA_CFLAGS = /MT /nologo /W3 $(SSLPA_INCLUDES) $(SSLPA_DEFINES) /c 


# ldnvfctl include paths
LDNVFCTL_INCLUDES = /I..\ldnvnet\sys /I$(LIBUSB_WIN32_DIR)\include 

all: $(OUTDIR) $(OUTDIR)\ldnvfctl.exe 

$(OUTDIR) :
    if not exist "$(OUTDIR)/$(NULL)" mkdir $(OUTDIR)

.c.obj:
    $(cc) $(cdebug) $(cflags) $(cvarsmt) $(LDNVFCTL_INCLUDES) $(SSLPA_CFLAGS) /Fo"$(OUTDIR)\\" /Fd"$(OUTDIR)\\" $**



## ldnvfctl dependencies
ldnvfctl_objs = $(OUTDIR)\main.obj 
sslpa_objs = $(OUTDIR)\sslpa\base\network.obj \
						$(OUTDIR)\sslpa\base\proto_mod.obj \
						$(OUTDIR)\sslpa\base\tcpconn.obj \
						$(OUTDIR)\sslpa\base\tcppack.obj \
						$(OUTDIR)\sslpa\base\pcap-snoop.obj \
						$(OUTDIR)\sslpa\common\lib\debug.obj \
						$(OUTDIR)\sslpa\common\lib\r_assoc.obj \
						$(OUTDIR)\sslpa\common\lib\r_data.obj \
						$(OUTDIR)\sslpa\common\lib\r_errors.obj \
						$(OUTDIR)\sslpa\common\lib\r_list.obj \
						$(OUTDIR)\sslpa\common\lib\r_replace.obj \
						$(OUTDIR)\sslpa\common\lib\r_time.obj \
						$(OUTDIR)\sslpa\ssl\ciphersuites.obj \
						$(OUTDIR)\sslpa\ssl\ssl.enums.obj \
						$(OUTDIR)\sslpa\ssl\ssl_analyze.obj \
						$(OUTDIR)\sslpa\ssl\ssl_rec.obj \
						$(OUTDIR)\sslpa\ssl\ssldecode.obj \
						$(OUTDIR)\sslpa\ssl\sslprint.obj \
						$(OUTDIR)\sslpa\ssl\sslxprint.obj \
						$(OUTDIR)\sslpa\null\null_analyze.obj


sslpa_linkobjs = $(OUTDIR)\network.obj \
								$(OUTDIR)\proto_mod.obj \
								$(OUTDIR)\tcpconn.obj \
								$(OUTDIR)\tcppack.obj \
								$(OUTDIR)\pcap-snoop.obj \
								$(OUTDIR)\debug.obj \
								$(OUTDIR)\r_assoc.obj \
								$(OUTDIR)\r_data.obj \
								$(OUTDIR)\r_errors.obj \
								$(OUTDIR)\r_list.obj \
								$(OUTDIR)\r_replace.obj \
								$(OUTDIR)\r_time.obj \
								$(OUTDIR)\ciphersuites.obj \
								$(OUTDIR)\ssl.enums.obj \
								$(OUTDIR)\ssl_analyze.obj \
								$(OUTDIR)\ssl_rec.obj \
								$(OUTDIR)\ssldecode.obj \
								$(OUTDIR)\sslprint.obj \
								$(OUTDIR)\sslxprint.obj \
								$(OUTDIR)\null_analyze.obj


$(OUTDIR)\ldnvfctl.exe: $(ldnvfctl_objs) $(sslpa_objs)
    $(link) $(ldebug) $(conlflags) $(ldnvfctl_objs) $(sslpa_linkobjs)\
    -out:$(OUTDIR)\ldnvfctl.exe  $(conlibsmt) $(SSLPA_LIBS) advapi32.lib kernel32.lib powrprof.lib $(LIBUSB_WIN32_DIR)\lib\msvc\libusb.lib
#		copy $(OUTDIR)\ldnvfctl.exe $(LDNVFCTL_INSTALLDIR)\.
#		copy .\libusb-win32-device-bin-0.1.12.1\bin\libusb0.dll $(LDNVFCTL_INSTALLDIR)\. 

clean:
	del $(OUTDIR)\*.exe
	del $(OUTDIR)\*.pdb
	del $(OUTDIR)\*.obj
	del $(OUTDIR)\*.idb
	
	
!ELSE
!MESSAGE This only builds for the Windows NT Platform
!ENDIF
