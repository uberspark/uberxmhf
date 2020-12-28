.. include:: /macros.rst


uhcalltest |uberapp| micro-hypervisor extension
===============================================

The following instructions show how the example |uberapp| 
``uxmhf/rgapps/linux/rgapp-uhcalltest`` (to test 
hypercalls) is built. 


#. Building ``uhcalltest`` on development system

::

   cd uxmhf/rgapps/linux/rgapp-uhcalltest
   make -w all


Copy ``uhcalltest`` to the target platform and execute with ``sudo ./uhcalltest``.

.. note::
   You must also enable uapp uhcalltest by using ``#define __UAPP_UHCALLTEST__`` within
   ``uxmhf/uobjcoll/main/include/xmhf-config.h`` when building
   the micro-hypervisor core as described in 
   :doc:`Build Micro-Hypervisor Core Framework </pc-intel-x86_32/build/build-core>`.
