.. include:: /macros.rst

Build Micro-Hypervisor Core Framework
=====================================

Execute the following, in order, within the ``uxmhf/`` folder in the root
tree of the sources:

#. 
   Generate the configure script

   ``./bsconfigure.sh``


#. 
   Configure the serial debug output

   ``./configure --enable-debug-serial=<your-serial-port-number> --with-debug-serial-maxcpus=<number-of-cores>``

   replace ``<your-serial-port-number>`` with the system serial port number (e.g., ``0x3f8`` for ``COM1``).
   replace ``<number-of-cores>`` with the number of cores on the platform that will run uxmhf. Note, that this is required when serial debugging is enabled. Also, it is not recommended to use tools such as ``nproc`` as the number of cores may differ between the build and target systems.


#. Building the uberobject binaries and the final hypervisor image

.. code-block:: bash

   ``make uxmhf-image``

If everything goes well then a final hypervisor image ``xmhf-x86-vmx-x86pc.bin.gz`` will be generated. Copy this to the target machine's ``/boot/``
