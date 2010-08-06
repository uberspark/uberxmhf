this document describes some pitfalls to avoid when installing
the tools required for building/testing the verifier

author: amit vasudevan (amitvasudevan@acm.org)

1. when using GNUARM tools (e.g, arm-elf-gcc) within cygwin you
need to ensure that LIBPATH and INCLUDE are set to null. This may
not be the default if you have .NET installed and the make process
will fail

2. when using the PHILIPS flasher, ensure "Enable DTR/RTS for
Reset and Bootloader selection" is checked before attempting to
flash. Without this, the flasher doesnt detect the DS2148WZ board.