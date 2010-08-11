# ldnvfctl makefile
# author: amit vasudevan (amitvasudevan@acm.org)

!IF "$(TARGETOS)" == "WINNT"

!include <Win32.Mak>

OUTDIR = .
LDNVFCTL_INSTALLDIR = e:\vpcvms\sharedfolder

all: $(OUTDIR) $(OUTDIR)\ldnvfctl.exe 

$(OUTDIR) :
    if not exist "$(OUTDIR)/$(NULL)" mkdir $(OUTDIR)

.c{$(OUTDIR)}.obj:
    $(cc) $(cdebug) $(cflags) $(cvarsmt) /I..\ldnvnet\sys /I.\libusb-win32-device-bin-0.1.12.1\include /Fo"$(OUTDIR)\\" /Fd"$(OUTDIR)\\" $**


## ldnvfctl dependencies

ldnvfctl_objs = $(OUTDIR)\main.obj 

$(OUTDIR)\ldnvfctl.exe: $(ldnvfctl_objs)
    $(link) $(ldebug) $(conlflags) $(ldnvfctl_objs) \
    -out:$(OUTDIR)\ldnvfctl.exe  $(conlibsmt) advapi32.lib kernel32.lib powrprof.lib .\libusb-win32-device-bin-0.1.12.1\lib\msvc\libusb.lib
		copy $(OUTDIR)\ldnvfctl.exe $(LDNVFCTL_INSTALLDIR)\.
		copy .\libusb-win32-device-bin-0.1.12.1\bin\libusb0.dll $(LDNVFCTL_INSTALLDIR)\. 

clean:
	del $(OUTDIR)\*.exe
	del $(OUTDIR)\*.pdb
	del $(OUTDIR)\*.obj
	
	
!ELSE
!MESSAGE This only builds for the Windows NT Platform
!ENDIF
