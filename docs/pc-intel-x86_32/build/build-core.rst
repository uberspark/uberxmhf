.. include:: /macros.rst

Build Micro-Hypervisor Core Framework
=====================================

Execute the following, in order, within the ``uxmhf/uobjcoll`` folder in the root
tree of the sources:


#. Setup build staging

   ``make stage``


#. Building the uberobject binaries and the final hypervisor image

::

   make clean
   make
   cd install && ./install.sh

If everything goes well then a final hypervisor image ``install/xmhf-x86-vmx-x86pc.bin.gz`` will be generated. 
Copy this to the target machine's ``/boot/``

Note that you can edit `uxmhf/uobjcoll/main/include/xmhf-config.h`
to enable certain build configuration parameters as neeeded:

#. ``#define __DMAP__`` to enable DMA protection capabilities
#. ``#define __XMHF_CONFIG_DEBUG_SERIAL_MAXCPUS__ NUMCPUS`` will set the
   number of CPUs for debug output. Here ``NUMCPUS`` is the total number of cores 
   on your platform. This setting is required when serial debugging is enabled as 
   below
#. ``#define __DEBUG_SERIAL__`` to enable debug output via UART; you must 
   additionally specify the debug port via ``#define DEBUG_PORT PORT_NUM``, where
   ``PORT_NUM`` is the debug port number (e.g., 0x3f8 for COM1)

