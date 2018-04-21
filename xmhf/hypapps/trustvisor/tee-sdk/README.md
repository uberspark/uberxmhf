# Overview

This is the Trusted-Execution-Environment Software-Development-Kit
(tee-sdk). It comprises tools and documentation for developing
_services_ that run in a trusted environments, and _clients_ that
communicate with those services, in Linux system. 
Initially, this means writing PALs that run under [TrustVisor](../), 
and applications that use PALs. However,
the APIs provided here are intended to provide sufficient abstraction
such that additional back-ends can be implemented, allowing services
and applications to be ported to use alternative trusted environments
with little or no modification.

# Terminology

Service
  ~ A piece of code running in a trusted execution environment
    provided by a _device_. (e.g., a PAL)
Client
  ~ An application that communicates with one or more _services_.
Device
  ~ A module providing a trusted execution environment (e.g., TrustVisor)

# Files

  * tz/: TrustZone API. This library is to be used by _clients_
    to communicate with _services_. This library supports multiple
    _device_ back-ends, abstracting them in such a way that most _client_
    code can be oblivious to which back-end is in use.
  * toolchain/: A cross-compiling toolchain for compiling
    and linking PALs. Implemented as wrappers around gcc.
  * ports/: Support libraries for _services_. These have been
    ported to run in a trusted environment provided by some _device_.
    i.e., they do not make system calls, and all dependencies should
    be satisfied by other ports, svcapi, or other libraries provided
    as part of this package.
  * examples/: Examples and tests.
  * doc/: Documentation.


# Documentation

  * [Installing SDK](doc/installing-sdk.md)
  * [Using SDK](doc/using-sdk.md)


