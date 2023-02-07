.. include:: /macros.rst


.. _uxmhfx86-build-intro:

Verifying and Building
======================

Building comprises of verifying and building the micro-hypervisor core 
configured with  selected functionality corresponding to |uberapp| micro-hypervisor extensions. 

An |uberapp| comprises of a legacy guest OS application 
(found within ``uxmhf/xmhf-rgapps/linux``)
and a micro-hypervisor extension (found within ``uxmhf/xmhf-uobjs/xh_*``)

.. toctree::
   :maxdepth: 4

   Software Requirements and Dependencies <build-swreq.rst>
   Verifying <build-verify.rst>
   Build micro-hypervisor core framework <build-core.rst>
   Adding new überApps <adding-uapps.rst>