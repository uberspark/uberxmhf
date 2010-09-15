# Microsoft Developer Studio Project File - Name="wpcap" - Package Owner=<4>
# Microsoft Developer Studio Generated Build File, Format Version 6.00
# ** DO NOT EDIT **

# TARGTYPE "Win32 (x86) Dynamic-Link Library" 0x0102

CFG=wpcap - Win32 Debug
!MESSAGE This is not a valid makefile. To build this project using NMAKE,
!MESSAGE use the Export Makefile command and run
!MESSAGE 
!MESSAGE NMAKE /f "wpcap.mak".
!MESSAGE 
!MESSAGE You can specify a configuration when running NMAKE
!MESSAGE by defining the macro CFG on the command line. For example:
!MESSAGE 
!MESSAGE NMAKE /f "wpcap.mak" CFG="wpcap - Win32 Debug"
!MESSAGE 
!MESSAGE Possible choices for configuration are:
!MESSAGE 
!MESSAGE "wpcap - Win32 Release" (based on "Win32 (x86) Dynamic-Link Library")
!MESSAGE "wpcap - Win32 Debug" (based on "Win32 (x86) Dynamic-Link Library")
!MESSAGE 

# Begin Project
# PROP AllowPerConfigDependencies 0
# PROP Scc_ProjName ""
# PROP Scc_LocalPath ""
CPP=cl.exe
MTL=midl.exe
RSC=rc.exe

!IF  "$(CFG)" == "wpcap - Win32 Release"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 0
# PROP BASE Output_Dir "Release"
# PROP BASE Intermediate_Dir "Release"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 0
# PROP Output_Dir "Release"
# PROP Intermediate_Dir "Release"
# PROP Ignore_Export_Lib 0
# PROP Target_Dir ""
# ADD BASE CPP /nologo /MT /W3 /GX /O2 /D "WIN32" /D "NDEBUG" /D "_WINDOWS" /D "_MBCS" /D "_USRDLL" /D "LIBPCAP_EXPORTS" /YX /FD /c
# ADD CPP /nologo /MT /W3 /GX /O2 /I "../libpcap/" /I "../libpcap/bpf" /I "../libpcap/lbl" /I "../libpcap/Win32/Include" /I "../libpcap/Win32/Include/ipv6kit" /I "../../common" /D "YY_NEVER_INTERACTIVE" /D yylval=pcap_lval /D "_WINDOWS" /D "_USRDLL" /D "LIBPCAP_EXPORTS" /D "HAVE_STRERROR" /D "NDEBUG" /D "__STDC__" /D "INET6" /D "WIN32" /D "_MBCS" /D SIZEOF_CHAR=1 /D SIZEOF_SHORT=2 /D SIZEOF_INT=4 /D HAVE_ADDRINFO=1 /YX /FD /c
# ADD BASE MTL /nologo /D "NDEBUG" /mktyplib203 /win32
# ADD MTL /nologo /D "NDEBUG" /mktyplib203 /win32
# ADD BASE RSC /l 0x410 /d "NDEBUG"
# ADD RSC /l 0x410 /d "NDEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo
LINK32=link.exe
# ADD BASE LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib /nologo /dll /machine:I386
# ADD LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib wsock32.lib /nologo /dll /machine:I386 /def:".\wpcap.def" /implib:"../lib/wpcap.lib"
# SUBTRACT LINK32 /pdb:none

!ELSEIF  "$(CFG)" == "wpcap - Win32 Debug"

# PROP BASE Use_MFC 0
# PROP BASE Use_Debug_Libraries 1
# PROP BASE Output_Dir "Debug"
# PROP BASE Intermediate_Dir "Debug"
# PROP BASE Target_Dir ""
# PROP Use_MFC 0
# PROP Use_Debug_Libraries 1
# PROP Output_Dir "Debug"
# PROP Intermediate_Dir "Debug"
# PROP Ignore_Export_Lib 0
# PROP Target_Dir ""
# ADD BASE CPP /nologo /MTd /W3 /Gm /GX /ZI /Od /D "WIN32" /D "_DEBUG" /D "_WINDOWS" /D "_MBCS" /D "_USRDLL" /D "LIBPCAP_EXPORTS" /YX /FD /GZ /c
# ADD CPP /nologo /MTd /W3 /Gm /GX /ZI /Od /I "../libpcap/" /I "../libpcap/bpf" /I "../libpcap/lbl" /I "../libpcap/Win32/Include" /I "../libpcap/Win32/Include/ipv6kit" /I "../../common" /D "YY_NEVER_INTERACTIVE" /D yylval=pcap_lval /D "_USRDLL" /D "LIBPCAP_EXPORTS" /D "HAVE_STRERROR" /D "_DEBUG" /D "__STDC__" /D "INET6" /D "WIN32" /D "_WINDOWS" /D "_MBCS" /D SIZEOF_CHAR=1 /D SIZEOF_SHORT=2 /D SIZEOF_INT=4 /D "HAVE_ADDRINFO" /FR /YX /FD /GZ /c
# ADD BASE MTL /nologo /D "_DEBUG" /mktyplib203 /win32
# ADD MTL /nologo /D "_DEBUG" /mktyplib203 /win32
# ADD BASE RSC /l 0x410 /d "_DEBUG"
# ADD RSC /l 0x410 /d "_DEBUG"
BSC32=bscmake.exe
# ADD BASE BSC32 /nologo
# ADD BSC32 /nologo
LINK32=link.exe
# ADD BASE LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib /nologo /dll /debug /machine:I386 /pdbtype:sept
# ADD LINK32 kernel32.lib user32.lib gdi32.lib winspool.lib comdlg32.lib advapi32.lib shell32.lib ole32.lib oleaut32.lib uuid.lib odbc32.lib odbccp32.lib wsock32.lib /nologo /dll /debug /machine:I386 /def:".\wpcap.def" /implib:"../lib/wpcap.lib" /pdbtype:sept
# SUBTRACT LINK32 /pdb:none

!ENDIF 

# Begin Target

# Name "wpcap - Win32 Release"
# Name "wpcap - Win32 Debug"
# Begin Source File

SOURCE=..\libpcap\bpf\net\bpf.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\bpf_dump.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\bpf\net\bpf_filter.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\bpf_image.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\etherent.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\ethertype.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Src\Ffs.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\gencode.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\gencode.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Src\getnetbynm.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Src\getnetent.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Src\getopt.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Src\getservent.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\Grammar.c
# End Source File
# Begin Source File

SOURCE=..\Include\Net\if.h
# End Source File
# Begin Source File

SOURCE=..\Include\Net\if_arp.h
# End Source File
# Begin Source File

SOURCE=..\Include\Netinet\If_ether.h
# End Source File
# Begin Source File

SOURCE=..\Include\Netinet\In_systm.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\inet.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Src\Inet_net.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Netinet\Ip.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Netinet\Ip_icmp.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Netinet\Ip_var.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Arpa\Nameser.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\nametoaddr.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Net\Netdb.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\optimize.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Net\Paths.h
# End Source File
# Begin Source File

SOURCE="..\libpcap\pcap-int.h"
# End Source File
# Begin Source File

SOURCE="..\libpcap\pcap-namedb.h"
# End Source File
# Begin Source File

SOURCE="..\libpcap\pcap-win32.c"
# End Source File
# Begin Source File

SOURCE=..\libpcap\pcap.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\pcap.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\ppp.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Rpc\Rpc_cut.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\savefile.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\Scanner.c
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Netinet\Tcp.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Netinet\Tcp_var.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Netinet\Tcpip.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Arpa\Tftp.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\libpcap\Tokdefs.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Netinet\Udp.h
# End Source File
# Begin Source File

SOURCE=..\libpcap\win32\Include\Netinet\Udp_var.h
# End Source File
# Begin Source File

SOURCE="..\Win32-Extensions\version.rc"
# End Source File
# Begin Source File

SOURCE="..\Win32-Extensions\Win32-Extensions.c"
# End Source File
# Begin Source File

SOURCE=.\wpcap.def
# PROP Exclude_From_Build 1
# End Source File
# Begin Source File

SOURCE=..\..\common\Packet.lib
# End Source File
# End Target
# End Project
