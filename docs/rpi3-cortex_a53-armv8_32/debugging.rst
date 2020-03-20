.. role:: raw-html-m2r(raw)
   :format: html


----

layout: page
tocref: uber eXtensible Micro-Hypervisor Framework Documentation &gt; rpi3-cortex_a53-armv8_32  

title: Installing
-----------------

Terminology
-----------


* ``host system`` -- system where the serial log is collected and examined.
* ``target system`` -- system where uberXMHF runs and ouputs debug information 
  via the serial port.

:raw-html-m2r:`<br/>`

Debugging Setup
---------------

uberXMHF (rpi3-cortex_a53-armv8_32) debugging is done primarily via the 
Raspberry PI 3 serial port.

You will need to purchase a USB to TTL serial cable such as the one 
available `here <https://www.adafruit.com/product/954?gclid=Cj0KCQjw_ODWBRCTARIsAE2_EvVn-6n_HsU-McCFk-ffkiPooqiDkVjVaZtq39GAIyy5s8Ep5yb6K9QaAtKQEALw_wcB>`_

Connect Pin 6 on PI to GND of serial cable; Pin 8 to RX and Pin 10 to TX.

See :doc:`Installing uberXMHF (rpi3-cortex_a53-armv8_32) <{% link docs/rpi3-cortex_a53-armv8_32/installing>` for how to install
the uberXMHF binaries on the SD card. In the 
*Deploying binaries to SD Card* section, perform the following on 
the ``host system`` where development is done:

.. code-block::

   1. Edit `~/mnt/pi-boot/config.txt` and add the following lines: 
       `enable_uart=1` 
       `init_uart_baud=115200` 
       `force_turbo=0`


Before powering up the PI 3 and performing a boot, do the following on
the ``host system`` in a seperate terminal (replace ttyUSB0 with the 
serial port of the USB to TTL adapter):

.. code-block::

   sudo screen /dev/ttyUSB0 115200 8N1
