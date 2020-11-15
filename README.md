# uber eXtensible Micro-Hypervisor Framework (uberXMHF)

## Introduction

The uber eXtensible Micro-Hypervisor Framework (uberXMHF)
is a formally verifiable micro-hypervisor framework 
which forms the foundation for a new class of (security-oriented) 
micro-hypervisor based applications ("uberapps") on commodity computing platforms.

uberXMHF currently runs on both x86 (Intel and AMD) and ARM (Raspberry PI) 
multi-core hardware virtualized platforms.
The framework is capable of running unmodified legacy multiprocessor 
capable OSes such as Windows and Linux.  

Visit: <http://uberxmhf.org> for more information on how to download, 
build, install, contribute and get involved.

The formatted documentation can 
be read online at: <http://uberxmhf.org/docs/toc.html>

Documentation sources are within `docs/` and are in reStructuredText (reST)
format. You can start reading the docs from `docs/index.rst` using any text 
editor of your choice. 

A html version of the documentation can also be built using
`make clean` followed by `make docs_html` within the `docs/` folder.
Note that you will need a working installation of sphinx to build
the documentation within your development environment. For example, 
within Ubuntu/Debian distributions the following will install sphinx:

`sudo apt install python3-pip`
`python3 -m pip install sphinx==2.2.0`
`python3 -m pip install sphinx-jsondomain==0.0.3`

uberSpark (<http://uberspark.org>) is used to build and verify 
security invariants of uberXMHF.


## Contacts, Maintainers and Contributors
* Amit Vasudevan [<http://hypcode.org>]
  * uberXMHF: pc-intel-x86-32 (Intel PC), 
  rpi3-cortex_a53_armv8_32 (Raspberry PI 3), and
  pc-lagacy-x86-32 (AMD PC, Intel PC (legacy))
  * libbaremetal and Lockdown

* Zongwei Zhou 
  * TrustVisor and tee-sdk

* Other contributors: Jonathan McCune, James Newsome, Ning Qu, and Yanlin Li


## Copying

The uberXMHF project comprises code from multiple sources, under multiple
open source licenses. See [COPYING.md](COPYING.md) for details.

