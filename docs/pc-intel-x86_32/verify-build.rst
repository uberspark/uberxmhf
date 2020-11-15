.. include:: /macros.rst


Verifying and Building
======================

Software Requirements and Dependencies
--------------------------------------

The uberSpark development and verification framework is required (available `here <https://uberspark.org>`_\ ). Note, these tools require a 64-bit environment, so the micro-hypervisor cannot be built locally.


Verfying
--------

Execute the following, in order, within the ``uxmhf/`` folder in the root
tree of the sources:


#. 
   Prepare for verification

   ``./bsconfigure.sh``

   ``./configure --disable-debug-serial``

   ``make uxmhf-verifyuobjs-prep``


#. 
   Verifying individual uberobjects

   ``cd xmhf-uobjs/<uobj-name>``

   ``make verify``

   ``cd ../..``

   replace ``<uobj-name>`` with the uberobject directory name (e.g., ``xh_hyperdep``\ )


#. 
   Verifying all the uberobjects

   ``make uxmhf-verifyuobjs-all``


Building
--------

Execute the following, in order, within the ``uxmhf/`` folder in the root
tree of the sources:


#. 
   Configure the serial debug output

   ``./configure --enable-debug-serial=<your-serial-port-number> --with-enable-serial-debug=<number-of-cores>``

   replace ``<your-serial-port-number>`` with the system serial port number (e.g., ``0x3f8`` for ``COM1``).
   replace ``<number-of-cores>`` with the number of cores on the platform that will run uxmhf. Note, that this is required when serial debugging is enabled. Also, it is not recommended to use tools such as ``nproc`` as the number of cores may differ between the build and target systems.


#. Building the uberobject binaries and the final hypervisor image

.. code-block:: bash

   ``make uxmhf-image``

If everything goes well then a final hypervisor image ``xmhf-x86-vmx-x86pc.bin.gz`` will be generated. Copy this to the target machine's ``/boot/``
