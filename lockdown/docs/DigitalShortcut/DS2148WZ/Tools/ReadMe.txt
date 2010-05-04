**** Tools ReadMe ****

- GNUARM(arm-elf)
From www.gnuarm.com (Files) download Binaries GCC-4.1 toolchain (Cygwin) 
GCC: file bu-2.17_gcc-4.1.1-c-c++_nl-1.14.0_gi-6.5.exe is installed automatically.
Before start uncheck "Cygwin options" checkbox.

Download make.exe for GNU and copy it to GNUARM\bin.

Cygwin: Run Setup.exe downloaded from Cygwin.com. Select "Install from Internet".
  Typicaly it doesn't require any changes or customizations, however based on the feedback
  from our customers we know that for some computers cygintl-2.dll library is required.
  For such cases run Setup again and in "Select Packages" window click on "+" in Libs 
  category and then select libint2 GNU Internationalization runtime library.

  Check cygwin1.dll if you have 1 file only. 
  Modify Path (in OS Environment Variables: MyComputer\Properties\Advanced\Environment Variables )
  to include Cygwin\bin.

Path example:
Path=C:\Tcl\bin;C:\WINDOWS\system32;C:\WINDOWS;C:\WINDOWS\system32\Wbem;C:Program Files\ZipGenius 6\;
  C:program files\gnuarm\bin; C:\cygwin\bin

Path Setting - Environment Variables: 
  Start->My Computer (Right Button)->Properties->Advanced->Environment Variables->Path->Edit

- ActiveTcl
Download Download ActiveTcl 8.5.x.x or newer for Windows file from www.activestate.com. 


- USB virtual serial com
Extract usbser.sys from \Windows\Driver Cache\i386\*.cab (sp2.cab) and 
   copy USBSER.INF. 

Win Vista USB virtual serial com: 
 - USBSER.INF modifications: add "include=mdmcpq.inf" to sections [GSerialInstall] & [GSerialInstall.Services]

Virtual com port identifiacation under Vista:
Connect USB Serial Device and check serial ports with
Control Panel->Administrative Tools->System Configuration->Tools->System Information(Launch)
	Components->Ports->Serial


- Philips Flash Loader
Unzip flash.isp.utility.lpc2000.zip and install it.
Philips Flash Utility (LPC2000 Flash Utility V2.2.3) Settings for DS2148WZ:
Connected to Port: COM1
Use Baud Rate: 38400
Use DTR/RTS for Reset...: Checked
Device: LPC2148
XTAL Freq[kHz]: 12000
After pressing ReadDevice ID button PartID should be 67305253


- Termite2.3 (Terminal Emulator)
Termite-2.3.exe installs the software. Settings are simple and obvious.


- Srecord package (by Peter Miller) is a collection of tools for bin, hex and other file formats conversions and manipulations.
Very useful when preparing files for Flash Loader.


- WireShark Network Protocol Analyzer
Download wireshark-setup-x.x.exe from www.wireshark.org/download and execute it.


- usbview. Usb port viewer. No installation required




