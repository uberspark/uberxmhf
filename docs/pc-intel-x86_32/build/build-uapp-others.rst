.. include:: /macros.rst


Other |uberapp| Micro-Hypervisor Extensions
===========================================

The following are other available |uberapp| micro-hypervisor extensions:

.. note::   you can enable these optional micro-hypervisor extensions by enabling
            the following definitions within the ``uberspark.uobjcoll.configdefs`` JSON
            node within ``uxmhf/uobjcoll/uberspark.json`` as needed:


#. ``uapp_aprvexec`` to enable a |uberapp| micro-hypervisor extension which provides approved code execution
#. ``uapp_hyperdep`` to enable a |uberapp| micro-hypervisor extension which provides data execution prevention
#. ``uapp_ssteptrace`` to enable a |uberapp| micro-hypervisor extension which provides single-step instruction tracing
#. ``uapp_syscalllog`` to enable a |uberapp| micro-hypervisor extension which provides system call logging.

The corresponding rich-guest applications can be found within 
``uxmhf/rgapps/linux/rgapp-*`` and can be built using:

::

   cd uxmhf/rgapps/linux/rgapp-<app>
   make -w all


..  note::
    Here `<app>` can be ``aprvexec``, ``hyperdep``, ``ssteptrace``, and ``syscalllog``
    corresponding to the micro-hypervisor extensions.


Copy the resulting binary to the target platform and execute with ``sudo``
privileges.
