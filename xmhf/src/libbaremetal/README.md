libbaremetal
============

libbaremetal is composed of several sub-libraries which provide,
libc stubs (think `string.h`'s mem*(), str*()); utility
functions (e.g., HPT abstraction, command line parameter parsing); 
TPM functions; and general cryptography routines (both asymmetric and
symmetric). The following are the included sub-libraries and their 
functionality:

* libxmhfc - minimalistic libc functions

* libxmhfutil - various utility functions (e.g., HPT abstraction and command line parameter parsing)

* libtpm - functions to interact with a (physical) TPM

* libtv_utpm - hypervisor-agnostic core logic of the TrustVisor hypapp's Micro-TPM implementation

* libxmhfcrypto - general cryptography routines

Building
========

libbaremetal and sub-libraries are typically built using an out-of-tree
build process as follows:

	cd mybuilddir
	make -f <path-to-libbaremetal-src>/Makefile

libbaremetal can also be built in-tree if needed as follows:

	make

this will result in the objects and sub-libraries being generated
in the `_objects` directory.

