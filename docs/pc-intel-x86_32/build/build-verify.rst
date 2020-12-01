.. include:: /macros.rst


Verfying
========

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
