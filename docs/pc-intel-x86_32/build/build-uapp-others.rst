.. include:: /macros.rst


Other |uberapp| Micro-Hypervisor Extensions
===========================================

The following are other available |uberapp| micro-hypervisor extensions:


.. note:: 
    You can enable these extensions by editing ``uxmhf/uobjcoll/main/include/xmhf-config.h``
    and enabling the appropriate definition while building the micro-hypervisor core framework. 


#. ``#define __UAPP_APRVEXEC__`` to enable a |uberapp| micro-hypervisor extension which provides approved code execution
#. ``#define __UAPP_HYPERDEP__`` to enable a |uberapp| micro-hypervisor extension which provides data execution prevention
#. ``#define __UAPP_SSTEPTRACE__`` to enable a |uberapp| micro-hypervisor extension which provides single-step instruction tracing
#. ``#define __UAPP_SYSCALLLOG__`` to enable a |uberapp| micro-hypervisor extension which provides system call logging.

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
