rem 
rem batchfile for building the lockdown trusted environment
rem virtual network adapter driver for windows
rem author: amit vasudevan (amitvasudevan@acm.org)
rem

set TEMP=c:\windows\temp
call c:\WinDDK\7600.16385.1\bin\setenv.bat c:\WinDDK\7600.16385.1\ chk WNET
rem e:
rem cd e:\amit\projects\lockdown\code\guestos\win2k3\ldnvnet\sys
cd c:\amit\projects\lockdown\code\guestos\win2k3\ldnvnet\sys
build -ceZ
				 
