.. include:: /macros.rst

Build Micro-Hypervisor Core Framework
=====================================

Execute the following, in order, within the ``uxmhf/uobjcoll`` folder in the root
tree of the sources:


#. Building the uberobject binaries and the final hypervisor image

::

   uberspark build -v
   cd install && ./install.sh

If everything goes well then a final hypervisor image ``install/xmhf-x86-vmx-x86pc.bin.gz`` will be generated. 
Copy this to the target machine's ``/boot/``

.. note::   you can enable optional core micro-hypervisor features by enabling
            the following definitions within the ``uberspark.uobjcoll.configdefs`` JSON
            node within ``uxmhf/uobjcoll/uberspark.json`` as needed:

.. note::   the option ``-v`` above, is optional and enables verbose debugging information
            for the |uspark| command line tool. 
            

#. ``dmap`` to enable DMA protection capabilities
#. ``xmhf_config_debug_serial_maxcpus`` will set the
   number of CPUs for debug output. You need to specify the total number of cores 
   on your platform. This setting is required when serial debugging is enabled as 
   below
#. ``debug_serial`` to enable debug output via UART; you must 
   additionally specify the debug port number via ``debug_port`` (e.g., 0x3f8 for COM1)
#. ``debug_memory`` to enable debug output to memory. One can use the following commands
   to locate its base address in bootloader and runtime:
   readelf -a ./_triage/uberspark/loaders/baremetal/x86_32/grub-legacy/_build/loader.exe | grep g_log_mem
   readelf -a ./_triage/uberspark/uobjcoll/platform/pc/uxmhf/uobjcoll.exe | grep g_log_mem
   For example, the first command outputs the address 1e12000 and the second one outputs 661c000
