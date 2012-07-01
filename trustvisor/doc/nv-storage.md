[TrustVisor](..) uses TPM NVRAM to securely store a master secret that is
used to derive its cryptographic keys. For a real deployment of
TrustVisor, this would need to be access controlled to TrustVisor's
measurement, so that untrusted software would be unable to access this
storage. However, since we have not yet implemented an *upgrade*
strategy, this is impractical. For now we set the relevant storage to
be access-controlled to "place-holder" PCRs (11 and 12 below, instead
of 17, 18, and possibly 19) that we don't actually extend with
anything.

Disable the infineon driver
===========================

Modern Ubuntu has a tendency to load the Infineon-specific v1.1b TPM
driver, when it should be using `tpm_tis`.  Thus, we blacklist
`tpm_infineon`.  Don't forget to reboot after making this change.  It
is possible to manually remove this driver (`modprobe -r
tpm_infineon`) and `modprobe tpm_tis`, if you know what you're
doing. In `/etc/modprobe.d/blacklist.conf` add

    blacklist tpm_infineon

Shut down trousers, if it is running
====================================

See if trousers is running first, shut down if necessary.  It will
probably start up again after the next reboot.  You may wish to
uninstall it or disable it more permanently if you're not otherwise
using it.

    /etc/init.d/trousers status
    /etc/init.d/trousers stop

Install jTpmTools
=================

Our current testing has been with v0.6 but we will soon move to
v0.7. <https://sourceforge.net/projects/trustedjava/files/jTPM%20Tools/>

    sudo dpkg -i jtpmtools_0.6.deb

Set the tpm device to be accessible by jtss
===========================================

    chown jtss:tss /dev/tpm0
    /etc/init.d/jtss start
    /etc/init.d/jtss status
 
    cat /var/log/jtss/tcs_daemon.log

Take ownership of the TPM
=========================

You will need to take ownership of the TPM, and set an owner
password. It is important not to lose the owner password that you
set. In TrustVisor's security model it is *not* security critical that
the owner password is not compromised, so feel free to use a well
known password or empty string if you are not using the TPM for other
purposes that might require a strong TPM owner password.

    jtt take_owner -e ASCII -o 'owner_password'

Define the NV spaces
====================

We actually define two nv spaces. One stores TrustVisor's master
secret. The other stores the root of a hash chain used for replay
protection (see [Memoir])

    jtt nv_definespace \
        --index 0x00015213 \
        --size 20 \
        -o 'owner_password' \
        -e ASCII \
        -p 11,12 \
        -w \
        --permission 0x00000000 \
        --writelocality 2 \
        --readlocality 2
    jtt nv_definespace \
        --index 0x00014e56 \
        --size 32 \
        -o 'owner_password' \
        -e ASCII \
        -p 11,12 \
        -w \
        --permission 0x00000000 \
        --writelocality 2 \
        --readlocality 2

Unload Linux TPM driver
=======================

Before running Trustvisor or PAL code that requires access to the NV
RAM, we need to ensure the Linux TPM device driver is indeed
removed. Hence, we want to stop all the drivers that rely on the Linux
TPM device driver.  This requirement will go away once issue 15 is
closed. <https://sourceforge.net/p/xmhf/tickets/15/>
 
    /etc/init.d/jtss stop
    modprobe -r tpm_tis