Introduction
============

Intel Active Management Technology (AMT) includes a virtual serial
port, called Serial-Over-LAN (SOL).

linux.die has a useful [AMT Howto](http://linux.die.net/man/7/amt-howto).

Following is a concrete set of steps for enabling and using AMT SOL on
an HP 8540p. These instruction likely apply to other hardware, as
well.

DISCLAIMERS
===========

* ***A lost AMT password cannot be reset***. AMT is implemented in the
     firmware and chipset of the machine, and is designed to allow an
     IT department to control a company's machines, *overriding the
     physically present user*. By design, physical presence is
     insufficient to reset the password if you lose it. When
     relinquishing ownership of a machine, make sure to tell the new
     owner the AMT password, or better-yet revert to the default
     password "admin" and disable AMT in the BIOS.

* ***A compromised AMT password is bad news***. AMT gives the power to
     update firmware, boot from a chosen device or network location,
     power cycle, and more. Choose a good password and be careful that
     it's not compromised.

* ***Using the directions below on an open network will compromise
     your AMT password***. We are using plaintext password
     authentication. An eavesdropper can easily grab it. I believe
     it's possible to enable encryption and stronger authentication;
     we should look into it.

Enable AMT in firmware
======================

You may need to enable AMT in the firmware. On the 8540p, you need to
go to turn on `system_config.amt_options.firmware_verbosity` and
`setup_prompt`.

Configure AMT
=============

Once AMT is enabled, you should see an AMT prompt during boot. Hit
`Ctrl-p` to enter AMT configuration. The default password is
'admin'. Once you've logged in:

* **You'll be forced to change the admin password**. Again, do not
    lose or compromise this password! The system will enforce some
    password rules. See the [AMT Howto](http://linux.die.net/man/7/amt-howto).
* **Setup the network**. It's best not to make AMT accessible from the
    open network, if possible. In my case, I'm using a direct ethernet
    connection between my two machines, so I statically configured the
    host machine to 192.168.0.2.
* **Activate the network**
* **Ensure serial-over-lan (SOL) is enabled**
* **Enable `legacy redirection mode` (or `SMB (Small Business)
    management mode`)** This enables a simpler network
    protocol. You'll need it to use `amtterm`. Unfortunately this also
    means we're doing password authentication and sending the password
    in the clear.

Point your code at the AMT serial port
======================================

You can use `dmesg | grep ttyS` to examine the serial ports that your
system now recognizes. On the 8540p the AMT serial port is recognized
as `ttyS0`, but is at address `0x6080` instead of the usual `0x3f8`.

Get amtterm
===========

Use amtterm 1.3 or higher. Older versions have bugs that effect
the ability to log output, and had more frequent disconnections.
It is available from
the author's [git repository](http://www.kraxel.org/cgit/amtterm/) or
[releases directory](http://www.kraxel.org/releases/amtterm/ releases
directory).

Connect from the client
=======================

In my case, since I'm using a direct ethernet connection, I need to
bring up the ethernet interface: `sudo ifconfig eth0
192.168.0.1`. You'll need to repeat this whenever the link goes down,
such as if the cable is unplugged, or either NIC resets (as on
reboot).

I use: `./amtterm 192.168.0.2 -p 'YourAMTpassword' | tee output-log.txt`

***CAUTION***: your AMT password gets sent in plaintext over the
   network. Do not do this on an open network.
