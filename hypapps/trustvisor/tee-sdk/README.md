# Overview

This is the Trusted-Execution-Environment Software-Development-Kit
(tee-sdk). It comprises tools and documentation for developing
_services_ that run in a trusted environments, and _clients_ that
communicate with those services. Initially, this means writing PALs
that run under TrustVisor, and applications that use PALs. However,
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

  * [tz](tz) TrustZone API. This library is to be used by _clients_
    to communicate with _services_. This library supports multiple
    _device_ back-ends, abstracting them in such a way that most _client_
    code can be oblivious to which back-end is in use.
  * [toolchain](toolchain) A cross-compiling toolchain for compiling
    and linking PALs. Implemented as wrappers around gcc.
  * [ports](ports) Support libraries for _services_. These have been
    ported to run in a trusted environment provided by some _device_.
    i.e., they do not make system calls, and all dependencies should
    be satisfied by other ports, svcapi, or other libraries provided
    as part of this package.
  * [examples](examples) Examples and tests.
  * [doc](doc) Documentation.


# Documentation

  * [Installing SDK](doc/installing-sdk.md)
  * [Using SDK](doc/using-sdk.md)

# Roadmap

## Clean API for developing services

We need to define a common clean interface for the runtime that
a device provides to a service. This is currently defined by
svcapi.h.

## Support for standalone service binaries

For the moment, services and the applications that interact with them
are compiled into the same binary. Support for standalone service
binaries will help decouple these. In the first iteration, these will
probably have to be statically compiled position-independent binaries.

The current API for loading services is trustvisor-specific, and
requires that the service (PAL) and the application that invokes it
are compiled into the same binary. Soon we'll standardize a standalone
binary format for services, so that they may be compiled separately
from the applications that use them. Ideally they will also be at least
source-compatible with alternative devices; perhaps even binary-compatible.

## User-space device

It should be fairly straightforward to create a device that runs a
service in user-space, while emulating both the functionality and
limitations of a trusted environment. This would help a lot with
debugging. A clean way to simulate this would be to fork a new process
to run the service code, passing data through shared mmap regions.

