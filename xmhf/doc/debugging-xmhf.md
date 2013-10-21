Terminology
===========

* `host system` -- system where the serial log is collected and examined.
* `target system` -- system where XMHF runs and ouputs debug information via the serial port.

Debugging Setup
===============

XMHF debugging is done primarily via the serial port.
See [Configuring Grub](configuring-grub.md) for how to pass serial
port configuration parameters to XMHF. 
You can use `dmesg | grep ttyS` on a Linux guest OS on the target 
system to examine the serial ports that the target system recognizes.

For machines without a physical 
serial port (e.g., laptops), you may leverage Intel Active Management 
Technology (AMT) Serial-Over-LAN (SOL) capability. AMT SOL exposes 
a serial port (.to the underlying platform once enabled (typically in
the BIOS).

Serial Debuging without AMT
---------------------------

* Connect the `host system` and the `target system` via a NULL serial
cable. 

* On the `target system` ensure that you pass the correct serial port
configuration parameters to XMHF (see [Installing XMHF](./installing-xmhf.md)).
A typical non-AMT configuration parameter will be similar to this: `serial=115200,8n1,0x3f8`

* On the `host system` run a terminal emulation program such as `minicom` (Ubuntu)
or `hyperterminal` (Windows). Ensure that the serial port configuration baud rate
and parity, data and stop bits match (e.g., `115200, 8n1`)

Serial Debugging with AMT
-------------------------

You will typically need to enable AMT in the BIOS/firmware of the `target system` . 
Since various BIOSes expose AMT in different ways, we will use the 
HP EliteBook 8540p/2540p laptop as a running example; the AMT specific instructions 
probably need a little adaptation on other platforms running AMT.

* Connect the `host system` and the `target system` via a regular ethernet
cable. This can be a cross-over cable (for direct connection) or a 
straight cable (if going via a switch/router).

* It is best not to make AMT accessible from an open network, since by default there is no encryption for password authentication. 
It seems possible to enable encryption and stronger authentication, but for our example we will assume a private network setup.
In our example, we statically configure the `host system` and 
`target system` to be on the private `192.168.0.0` network.

* Enable AMT in the BIOS/firmware on the `target system`. On the 8540p, you need to turn on 
`system_config -> amt_options -> firmware_verbosity -> setup_prompt`.

* Once AMT is enabled, you should see an AMT prompt during boot of the `target system`. 
Enter the AMT configuration; on the 8540p, hit
`Ctrl-p` to enter AMT configuration. The default password is
'admin'. Once you've logged in:

    * **You'll be forced to change the admin password**. Take care not
    lose or compromise this password! The system will enforce some
    password rules. See this [AMT Howto](http://linux.die.net/man/7/amt-howto) for more information.
    * **Setup the AMT IP**. In our example, we statically configure the
    `target system` to have the IP `192.168.0.2`
    * **Activate the network**
    * **Ensure serial-over-lan (SOL) is enabled**
    * **Enable `legacy redirection mode` (or `SMB (Small Business)
    management mode`)** This enables a simpler network
    protocol. You'll need it to use `amtterm`. 
    
* On the `target system` ensure that you pass the correct serial port
configuration parameters to XMHF (see [Installing XMHF](./installing-xmhf.md)).
A typical AMT serial configuration parameter will be similar to this: `serial=115200,8n1,0x6080`

* On the `host system`, install `amtterm` to obtain the serial debugging
messages
    
    * Use amtterm 1.3 or higher. Older versions have bugs that effect
the ability to log output, and have more frequent disconnections.
It is available from the [amtterm git repository](http://www.kraxel.org/cgit/amtterm/)
or [amtterm releases directory](http://www.kraxel.org/releases/amtterm/).
	
	* Connect to the `target system` by using the following command: `./amtterm 192.168.0.2 -p 'YourAMTpassword' | tee output-log.txt`. 
	Note: you may have to bring up the ethernet interface on the `host system` prior to issuing the above command. This can be done
	via `sudo ifconfig eth0 192.168.0.1` (assuming the `host system` IP is `192.168.0.1`).
	
