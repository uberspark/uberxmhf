# uberXMHF x86-32 AMD PC, x86-32 Intel PC (legacy)

uberXMHF x86-32 AMD PC, x86-32 Intel PC (legacy) includes the hypervisor 
framework and supporting libraries along with several example uberapps:

* [XMHF](xmhf): The eXtensible and Modular Hypervisor Framework 
  supporting custom hypervisor-based solutions (called "uberapps").

    * [libbaremetal](xmhf/src/libbaremetal): Utility functions used across modules,
     including minimal libc functionality, error-handling, TPM functions, 
     cryptographic routines, etc. As the name implies, this library is intended primarily for
     use in "bare metal" environments.

XMHF includes several example uberapps including 
full-fledged uberapps such as TrustVisor and Lockdown:
 
* [TrustVisor](hypapps/trustvisor): A special-purpose uberapp that provides
  code integrity as well as data integrity and secrecy for userspace
  Pieces of Application Logic (PALs).

    * [tee-sdk](hypapps/trustvisor/tee-sdk): The Trusted Execution Environment Software
      Development Kit. This is a set of tools and APIs for developing
      PALs and applications that use them.

* [Lockdown](hypapps/lockdown): An uberapp that provides the user with a red/green
  system: an isolated and constrained environment for performing
  online transactions, as well as a high-performance, general-purpose
  environment for all other (non-security-sensitive) applications. An
  external device verifies which environment is active and allows the
  user to securely learn which environment is active and to switch
  between them.







