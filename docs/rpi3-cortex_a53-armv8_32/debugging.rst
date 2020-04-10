.. include:: /macros.rst


Debugging
=========

Terminology
-----------


* ``host system`` -- system where the serial log is collected and examined.
* ``target system`` -- system where uberXMHF runs and ouputs debug information 
  via the serial port.


Debugging Setup
---------------

uberXMHF (rpi3-cortex_a53-armv8_32) debugging is done primarily via the 
Raspberry PI 3 serial port using a USB to TTL serial cable.

There are two types of USB to TTL serial cables available:

* *without* hardware-flow control (RTS/CTS) pins such as the one available 
  `here <https://www.adafruit.com/product/954>`_. This cable has four wires:
  red (power), black (ground), white (TX out of PI), and green (RX into PI). 
  The following
  is the connection to the PI 40-pin header:
 
  * Physical Pin 6  <--> ground (black) of serial cable
  * Physical Pin 8  <--> TX out of PI (white) of serial cable 
  * Physical Pin 10 <--> RX into PI (green) of serial cable

* *with* hardware-flow control (RTS/CTS) pins such as the one available 
  `here <https://www.adafruit.com/product/70>`_. This cable has six wires:
  black (ground), brown (CTS), red (power, 5V), orange (RXD into PI), yellow (TXD out of PI), green (RTS). The following
  is the connection to the PI 40-pin header:

  * Physical Pin 6  <--> ground (black) of serial cable
  * Physical Pin 8  <--> TXD out of PI (yellow) of serial cable
  * Physical Pin 10 <--> RXD into PI (orange) of serial cable
  * Physical Pin 11 <--> CTS (brown) of serial cable
  * Physical Pin 36 <--> RTS (green) of serial cable




See :doc:`Installing uberXMHF (rpi3-cortex_a53-armv8_32) </rpi3-cortex_a53-armv8_32/installing>` for how to install
the uberXMHF binaries on the SD card. In the 
*Deploying binaries to SD Card* section, perform the following on 
the ``host system`` where development is done:

Edit ``~/mnt/pi-boot/config.txt`` and add the following lines: 

.. code-block:: bash

    enable_uart=1 
    init_uart_baud=115200 
    force_turbo=0


Before powering up the PI 3 and performing a boot, do the following on
the ``host system`` in a seperate terminal (replace ttyUSB0 with the 
serial port of the USB to TTL adapter):

.. code-block:: bash

   sudo screen /dev/ttyUSB0 115200 8N1
