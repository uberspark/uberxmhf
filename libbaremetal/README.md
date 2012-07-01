libbaremetal is composed of several sub-libraries (`libxmhfc`,
`libxmhfutil`, `libtv_utpm`, `libxmhfcrypto`) which provide,
respectively: libc stubs (think `string.h`'s mem*(), str*()); utility
functions (e.g., HPT abstraction, command line parameter parsing); the
hypervisor-agnostic core logic of TrustVisor's Micro-TPM
implementation; and general cryptography routines (both asymmetric and
symmetric).
