Downgrade from Grub 2 to Grub 1
===============================

[XMHF](..) is currently only supported using Grub 1. If Grub 2 is already
installed (as it typically is on recent Linux distributions), you will
need to downgrade to Grub 1.

On Ubuntu: <http://ubuntuforums.org/showthread.php?t=1298932>

On Debian: <http://forums.debian.net/viewtopic.php?f=17&t=50132>

Quick and dirty instructions, on Ubuntu:

    sudo apt-get purge grub* os-prober
    sudo apt-get purge grub-gfxpayload-lists
    sudo apt-get install grub
    sudo update-grub
    grub-install /dev/sda
 
And remove lines from `/boot/grub/menu.lst`:

    title          Chainload into GRUB 2
    root           b5912383-7f9e-4911-b51d-b14ce8cea70b
    kernel         /boot/grub/core.img

Get the correct SINIT module (Intel only)
=========================================

[XMHF](..) launches itself with a *dynamic root of trust*. On Intel
platforms, this requires a signed SINIT module provided by Intel.

SINIT modules can be found here:
<http://software.intel.com/en-us/articles/intel-trusted-execution-technology/>

Grub settings
=============

Adding a Grub entry
-------------------

You will need to add a Grub entry to `/boot/grub/menu.lst`. To ensure
that it doesn't get clobbered, put it ***outside the AUTOMAGIC KERNEL
LIST***.

### Grub entry to boot Linux

To boot a Linux guest, we create a grub entry that loads the
hypervisor, and then re-loads grub. When booting the machine, first
choose the EMHF entry, and then choose a normal Linux entry.

A grub entry for emhf should look something like this:

    title XMHF
        rootnoverify (hd0,1)                         # should point to /boot
        kernel /init-x86.bin serial=115200,8n1,0x3f8 # substitute in the correct serial address
        module /hypervisor-x86.bin.gz
        modulenounzip (hd0)+1                        # should point to where grub is installed

On Intel it is necessary to append one more line to provide the SINIT
Authenticated Code module, or "ACmod". This should be the *last*
line. E.g.,

        module /i5_i7_DUAL_SINIT_18.BIN

SINIT modules can be found here:
<http://software.intel.com/en-us/articles/intel-trusted-execution-technology/>

This will boot XMHF with debug output going to the specified serial
port, and then reload grub.

### Grub entry to boot Windows

To boot Windows, configure XMHF to load the Windows boot sector
instead of recursively loading grub. Do this by modifying the
`modulenounzip` line to point to the partition where Windows is
installed instead of pointing to the MBR. For example, if Windows is
installed on `/dev/sda3`:

    title Windows on XMHF
        rootnoverify (hd0,1)                         # should point to /boot
        kernel /init-x86.bin serial=115200,8n1,0x3f8 # substitute in the correct serial address
        module /hypervisor-x86.bin.gz
        modulenounzip (hd0,2)+1                        # point to Windows partition

The rest of the settings are the same as for Linux, above. Again, you
will need to add a line for the SINIT module on Intel platforms.

savedefault for unattended boot
-------------------------------

Booting linux involves loading the grub menu twice. The first time you
must select the XMHF entry, and the second time you must select an OS
entry. You can automate this by using savedefault.

Set grub to boot the saved default:

    default         saved

Have your XMHF entry and what you want as your default OS entry save
each-other as the new default:

    title XMHF
        savedefault 1

    title Default OS
        savedefault 0

The parameter to savedefault is the menu entry that you would like as
the new default.

controlling grub remotely using the serial port
-----------------------------------------------

You'll need another machine that is connected to the target machine
with a serial connection. Note that if the target machine supports
Serial-Over-LAN, you can use that.

Tell grub your desired serial port settings:

    serial --port=0x3f8 --speed=115200

Tell grub to present its menu both over the serial port and the normal
console:

    terminal serial console

An unfortunate side-effect of this configuration is that grub will
hang forever until you press a key on one interface or the other. I'm
not sure whether there's a way to make it time out and pick one. If
you always want to use the serial port, you can probably leave off the
'console', which I would guess then skips this 'press a key' step.