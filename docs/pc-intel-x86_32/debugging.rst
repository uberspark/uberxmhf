.. include:: /macros.rst


Debugging
=========

Terminology
-----------


* ``host system`` -- system where the serial log is collected and examined.
* ``target system`` -- system where XMHF runs and ouputs debug information via the serial port.


Debugging Setup
---------------

XMHF debugging is done primarily via the serial port.
See :doc:`Installing uberXMHF (pc-intel-x86_32) </pc-intel-x86_32/installing>` for how to pass serial
port configuration parameters to XMHF. 

You can use ``dmesg | grep ttyS`` on a Linux guest OS on the target 
system to examine the serial ports that the target system recognizes.

For machines without a physical 
serial port (e.g., laptops), you may leverage Intel Active Management 
Technology (AMT) Serial-Over-LAN (SOL) capability. AMT SOL exposes 
a serial port to the underlying platform once enabled (typically in
the BIOS).

Serial Debuging without AMT
^^^^^^^^^^^^^^^^^^^^^^^^^^^

* 
  Connect the ``host system`` and the ``target system`` via a NULL serial
  cable. 

* 
  On the ``target system`` ensure that you pass the correct serial port
  configuration parameters to XMHF (see :doc:`Installing uberXMHF (pc-intel-x86_32) </pc-intel-x86_32/installing>`\ ).
  A typical non-AMT configuration parameter will be similar to this: ``serial=115200,8n1,0x3f8``

* 
  On the ``host system`` run a terminal emulation program such as ``minicom`` (Ubuntu)
  or ``hyperterminal`` (Windows). Ensure that the serial port configuration baud rate, parity, data and stop bits match (e.g., ``115200, 8n1``\ )

Serial Debugging with AMT
^^^^^^^^^^^^^^^^^^^^^^^^^

You will typically need to enable AMT in the BIOS/firmware of the ``target system`` . 
Since various BIOSes expose AMT in different ways, we will use the 
HP EliteBook 8540p/2540p laptop as a running example; the AMT specific instructions 
probably need a little adaptation on other platforms running AMT.


* 
  Connect the ``host system`` and the ``target system`` via an ethernet
  cable. This can be a cross-over cable (for direct connection) or a 
  straight cable (if going via a switch/router).

* 
  It is best not to make AMT accessible from an open network, since by default there is no encryption for password authentication. 
  It seems possible to enable encryption and stronger authentication, but for our example we will assume a private network setup.
  In our example, we statically configure the ``host system`` and 
  ``target system`` to be on the private ``192.168.0.0`` network.

* 
  Enable AMT in the BIOS/firmware on the ``target system``. On the 8540p, you need to turn on 
  ``system_config -> amt_options -> firmware_verbosity -> setup_prompt``.

* 
  Once AMT is enabled, you should see an AMT prompt during boot of the ``target system``. 
  Enter the AMT configuration; on the 8540p, hit
  ``Ctrl-p`` to enter AMT configuration. The default password is
  'admin'. Once you've logged in:


  * **You'll be forced to change the admin password**. Take care not
    lose or compromise this password! The system will enforce some
    password rules. See this `AMT Howto <http://linux.die.net/man/7/amt-howto>`_ for more information.
  * **Setup the AMT IP**. In our example, we statically configure the
    ``target system`` to have the IP ``192.168.0.2``
  * **Activate the network**
  * **Ensure serial-over-lan (SOL) is enabled**
  * **Enable ``legacy redirection mode`` (or ``SMB (Small Business)
    management mode``\ )** This enables a simpler network
    protocol. You'll need it to use ``amtterm``. 

* 
  On the ``target system`` ensure that you pass the correct serial port
  configuration parameters to XMHF (see :doc:`Installing uberXMHF (pc-intel-x86_32) </pc-intel-x86_32/installing>`\ ).
  A typical AMT serial configuration parameter will be similar to this: ``serial=115200,8n1,0x6080``

* 
  On the ``host system``\ , install ``amtterm`` to obtain the serial debugging
  messages


  * 
    Use amtterm 1.3 or higher. Older versions have bugs that effect
    the ability to log output, and have more frequent disconnections.
    It is available from the `amtterm git repository <http://www.kraxel.org/cgit/amtterm/>`_
    or `amtterm releases directory <http://www.kraxel.org/releases/amtterm/>`_.

  * 
    Connect to the ``target system`` by using the following command: ``./amtterm 192.168.0.2 -p 'YourAMTpassword' | tee output-log.txt``. 
    Note: you may have to bring up the ethernet interface on the ``host system`` prior to issuing the above command. This can be done
    via ``sudo ifconfig eth0 192.168.0.1`` (assuming the ``host system`` IP is ``192.168.0.1``\ ).


Debugging via Intel Direct Connect Interface (DCI)
---------------

One can use the following settings to debug uberXMHF on a modern hardware.

* Host PC: Win10 x64, USB 3.0 ports, Intel System Debugger NDA U2110.
* Target PC: Gigabyte Z390 Designare (bios: mb_bios_z390-designare_f8), i9 9900K, USB 3.0 ports (I did not try USB 3.1 and so on)


Prepare the target PC
^^^^^^^^^^^^^^^^^^^^^^^^^
* Flash the f8 bios

* On the host PC, run `UEFITool <https://codeload.github.com/LongSoft/UEFITool/zip/refs/tags/A58>`_ and open the bios image "Z390DESI.F8". Under the File menu, click Search and search GUID: 899407D7-99FE-43D8-9A21-79EC328CAC21. This is the "Setup" UEFI variable. Right click the section and select "Extract Body", save the section to a new file "section.bin".

* On the host PC, run `IFRExtractor <https://github.com/LongSoft/Universal-IFR-Extractor/releases/download/v0.3.6/IRFExtractor_0.3.6_win.zip>`_, open "section.bin" and export the human readable variable options "section IFR.txt" in the same folder.

* On the host PC, open "section IFR.txt" and find the following variables, their offsets, and values that should be picked. My example is as follows:

.. code-block:: bash

  * Platform Debug Consent   					offset:0x10d5    	set to 3
  * USB3 Type-C UFP2DFP Kernel/Platform Debug Support		offset:0xa0b    	set to 1
  * USB Overcurrent Override for DbC      			offset:0xa0c    	set to 1
      - Set {0A 82} to 0
  * CPU Run Control						offset:0x65f    	set to 1
  * CPU Run Control Lock					offset:0x660    	set to 0
  * Enable/Disable IED (Intel Enhanced Debug)			offset:0x8ec    	set to 1
  * xDCI Support						offset:0xa43    	set to 1

Especially, {0A 82} is due to the description "Suppress If {0A 82}" in the file "section IFR.txt". The referred document 1 says that "There might also be a section around these variables that you need to take into account: If there is i.e.: "Suppress If {0A 82}" , then you also have to memorize that address, it needs to be set so that the Debug variables are initialized: 0xa82 leads to VarStore and the definition of it shows "enabed if 1", therefore it later has to be set to "0""

* Create a UEFI boot flash drive with `ru.efi <https://github.com/JamesAmiTw/ru-uefi/>`_. One needs to format the flash drive with FAT32, make directory "efi/boot" and rename "ru.efi" to be "Bootx64.efi". We use this software to modify the BIOS image on the target PC.

* (Re-)Boot the target PC, run the renamed "ru.efi" from the flash drive. Use "pgdown" "pgup" to navigate UEFI variables and find the varible "Setup". Then we use "ctrl-pgdown" "ctrl-pgup" to access its content. This variable is 0x1xxx in size. Use the offset and values we found earlier to modify the content here. Use ctrl+w to save. Press alt+F to go to menus and quit after modifications are done.

* Reboot and connect the debug cable. The host PC must connect the cable via a native USB connection. That is, the connection starts from the host's USB port and ends on the target's USB. USB muxes/re-timers/repeaters/hubs are not recommended to exist in the path. In my test, going through USB hubs causes connection problems.


Run Intel System Debugger on host PC
^^^^^^^^^^^^^^^^^^^^^^^^^
* Run "Intel System Debugger Target Indicator 2021 NDA U2110", check if the connection is good.

* Run Intel System Debugger. First click the "New Connection" dropbox

* Then select "Connect and detect target". Use default settings and then click "Finish"

* Now the connection panel shows this:
Example shell output is:

.. code-block:: bash

  [INFO    ] Using workspace directory 'E:/workspaces/system_debugger/workspace/isd_cli/8ff45f4c-3686-49dc-b3dc-17c877f6eb
  62' for console session

  Welcome to the Intel(R) System Debugger CLI
          Python   (v3.6.10) 'D:\IntelSWTools\system_debugger\2110-nda\tools\python3\python.exe'
          IPython  (v7.13.0)
          colorama [Loaded]

  Modules:
          isd          - Intel(R) System Debugger CLI (v3.0.4673) [Loaded]
          tca          - Target Connection Assistant CLI (v3.0.4673) [Loaded]
          ipccli       - OpenIPC CLI (v1.2105.2135.100) [Loaded]
          sysdbg       - System Debug CLI (v1.21074+86b32) [Loaded]
          trace        - System Trace CLI (v1.2107.1906.200) [Loaded]
          crashlog     - Intel(R) Crash Log Framework (v3.42.21084.200) [Loaded]
          trace_agent  - System Trace Target Agent CLI [Loaded]


  [INFO    ] OpenIPC configuration 'CFL_CNP_DCI_USB'; probe plug-in(s): 'OpenDCI'
  [INFO    ] DCI: A DCI device has been detected, attempting to establish connection
  [INFO    ] DCI: Target connection has been fully established
  [INFO    ] Added new debug port 0 using probe plug-in 'OpenDCI'
  [INFO    ] Detected CNP B0 (H) on JTAG chain 0 at position 0
  [INFO    ] Detected CFL_M_UC R0 on JTAG chain 1 at position 0
  [INFO    ] Target state changed - Checking Target
  --- Logging error ---
  Traceback (most recent call last):
    File "D:\IntelSWTools\system_debugger\2110-nda\tools\python3\lib\logging\__init__.py", line 996, in emit
      stream.write(msg)
  UnicodeEncodeError: 'gbk' codec can't encode character '\xae' in position 119: illegal multibyte sequence
  Call stack:
    File "D:\IntelSWTools\system_debugger\2110-nda\tools\python3\lib\site-packages\intel\tcacli\logging.py", line 68, in _
  print
      self._logger.handle(log_record)
  Message: 'Trying to map detected components to targets: 8th Gen Intel? Core? processor (Coffee Lake S) R0, Intel 300 Ser
  ies Chipset (Cannon Point PCH-H) B0'
  Arguments: []
  --- Logging error ---
  Traceback (most recent call last):
    File "D:\IntelSWTools\system_debugger\2110-nda\tools\python3\lib\logging\__init__.py", line 996, in emit
      stream.write(msg)
  UnicodeEncodeError: 'gbk' codec can't encode character '\xae' in position 149: illegal multibyte sequence
  Call stack:
    File "D:\IntelSWTools\system_debugger\2110-nda\tools\python3\lib\site-packages\intel\tcacli\logging.py", line 68, in _
  print
      self._logger.handle(log_record)
  Message: "Detected known target 'Coffee Lake S / Cannon Point PCH-H' with components: 8th Gen Intel? Core? processor (Co
  ffee Lake S) R0 and Intel 300 Series Chipset (Cannon Point PCH-H) B0"
  Arguments: []
  [INFO    ] Detected known target 'Coffee Lake S / Cannon Point PCH-H' with components: 8th Gen Intel? Core? processor (C
  offee Lake S) R0 and Intel 300 Series Chipset (Cannon Point PCH-H) B0
  --- Logging error ---
  Traceback (most recent call last):
    File "D:\IntelSWTools\system_debugger\2110-nda\tools\python3\lib\logging\__init__.py", line 996, in emit
      stream.write(msg)
  UnicodeEncodeError: 'gbk' codec can't encode character '\xae' in position 91: illegal multibyte sequence
  Call stack:
    File "D:\IntelSWTools\system_debugger\2110-nda\tools\python3\lib\site-packages\intel\tcacli\logging.py", line 68, in _
  print
      self._logger.handle(log_record)
  Message: 'Components: \n\tCPU: 8th Gen Intel? Core? processor (Coffee Lake S) available.\n\tPCH: Intel 300 Series Chipse
  t (Cannon Point PCH-H) available.'
  Arguments: []
  [INFO    ] Components:
          CPU: 8th Gen Intel? Core? processor (Coffee Lake S) available.
          PCH: Intel 300 Series Chipset (Cannon Point PCH-H) available.
  [INFO    ] Target state changed - Available
  [INFO    ] IPC-CLI: 1.2105.2135.100, OpenIPC:Main (rev 661986) : 1.2106.5146.200
  In [1]: 


* Then create a new debug configuration, see the `link <https://software.intel.com/content/www/us/en/develop/documentation/system-debug-user-guide/top/intel-system-debugger-startup/launching-the-debugger.html>`_

* Now one can debug the system, see the `link <https://software.intel.com/content/www/us/en/develop/documentation/system-debug-user-guide/top/debugging-basics.html>`_

Reference
^^^^^^^^^^^^^^^^^^^^^^^^^
Same tutorial with figures, see https://github.com/superymk/docs/blob/main/IntelDCI/setup.md
