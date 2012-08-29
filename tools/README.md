Regression Testing
==================

Scripts
-------

See the contents of: `xmhf/tools/reg-test`

All of the documentation below tries to describe the environment where these scripts have the opportunity to do their thing.

`driver-scripts/nightly.sh` is the "main" script; it is a good place to start.

Disk image support
------------------

It is desirable to be able to boot a consistent configuration for testing.  Using network boot and a diskless test host, this can be achieved.  Using iSCSI and gPXE, the network block device (note: iSCSI is a protocol for network block devices, to be contrasted with something like NFS, which is a network file-system.  Block device is a lower-level abstraction than file-system) appears as a BIOS drive and grub 1.x and XMHF are confirmed to work just fine.

Using Linux as an iSCSI target (server) allows us to use Linux LVM2 (Logical Volume Management) to maintain snapshots of "golden" configurations, which can readily be cloned for individual test systems.  Separating /boot from / allows / to be common across many hosts, with per-host configuration only for /boot, resulting in easier maintenance and better performance (though no benchmarks have been run to confirm this).

Diskless / LiveCD-style Linux is commonplace, and there are a multitude of possibilities for the root filesystem (entire system in ramdisk, NFS, iSCSI, AFS, SAMBA, etc).  Linux really does not constrain how the root filesystem image is maintained.  Thus, let's allow the design we settle on for Linux to be influenced by the requirements that Windows imposes here.

### For Windows ###
* Windows 7 / Windows Server 2008 can be booted in a diskless configuration using [iSCSI](http://en.wikipedia.org/wiki/ISCSI) for the root filesystem.  
* There are ways to make this work for older versions of Windows as well, but they are more labor-intensive.  [Jon's consolidated HOWTO](http://jonmccune.wordpress.com/2011/12/19/diskless-windows-7-with-iscsi-and-gpxe/).
* So far a clean design for something in the spirit of aufs/custom-boot-partition is elusive.  So far the best option is to take advantage of LVM support in Linux to image the backend of the Windows filesystem that gets mounted via iSCSI.
* ***Windows is not currently supported for automated regression testing.***

### For Linux ###
* Use PXE to grab gPXE to boot via an iSCSI block device.  `/boot` iSCSI block device is unique per test host for three reasons:
    * Intel systems require a specific SINIT module, 
    * 'savedefault' writes to the MBR and I worry this could clobber the partition table in a particular race between multiple hosts, 
    * The iSCSI Initiator "iqn..." needs to be unique per Initiator
    * ***UPDATE*** Driving the grub config across the serial connection using [`expect`](http://www.linux-mag.com/id/699/) works with a real serial connection or with `amtterm`.  That solves all three of these problems.  ***TODO***: ditch the myriad `/boot` partitions. 
        * As of 2012-07-05, AMD systems boot directly out of the root filesystem without a distinct `/boot` device, while Intel systems still use a per-host `/boot` partition.  This is not necessary, so long as all of the relevant SINIT modules reside in the root filesystem's `/boot` directory.
* DHCP presents gPXE with a per-test-host (identified based on Ethernet MAC address) URL from which gPXE fetches iSCSI configuration information.  This iSCSI configuration information provides root filesystem (/, and includes `/boot`).
    * See `/home/driver/public_html/gpxe_slashboot_script*` on host `squid`.
* We use aufs (Another UnionFS; the "magic" filesystem overlay mechanism that lets LiveCDs appear to have writeable storage) and a ramdisk to present the illusion of volatile disk storage (with [aufsRootFileSystemOnUsbFlash](https://help.ubuntu.com/community/aufsRootFileSystemOnUsbFlash) script).  
* Test scripts that run on the individual test hosts are responsible for persisting interesting test results.
    * It is important that each test uploads its results right away, in case the next test crashes the system.
    * Test results get copied via `scp` to `logger@squid:/var/www/logger`.  The root filesystem image for the test hosts includes an SSH key that enables this to work seamlessly.

### Theory of [iSCSI boot](http://www.held.org.il/blog/2010/10/booting-linux-from-iscsi/) ###

1. The BIOS or NIC send a DHCP request to set-up the IP network settings and find a network bootable server, using the PXE-UNDI mechanisms
+ gPXE image is found, and downloaded using TFTP. gPXE sends yet another DHCP request and should now find the iSCSI address of the remote boot disk
+ gPXE starts as an iSCSI initiator that logs in to the iSCSI target, reads the remote boot disk's MBR and starts its boot loader (grub)
+ grub loads the kernel and initrd
+ initrd sends yet another DHCP request, sets up the IP network, and uses the iscsistart script, which sets up the iscsi initiator and logins (yes, again) to the iscsi target.
+ iscsistart script then mounts this disk and uses pivot_root (as usual) to make it the new root
+ boot process starts from the real root now, running `/sbin/init`.

### iSCSI cheat sheet ###

1. Discover what iSCSI Targets exist on server 10.0.0.1:
  `iscsiadm -m discovery -t st -p 10.0.0.1`
+ Connect to a particular Target (check `dmesg` for new `/dev/sdX` or use UUID if you already know what it should be)
  `iscsiadm -m node --targetname "iqn.2012-01.com.nfsec:iscsi.slashboot.caisson" --portal "10.0.0.1:3260" --login`
+ View active iSCSI sessions:
  `iscsiadm -m session -P 1`
+ Disconnect from a Target (you'd better have unmounted anything that you mounted on /dev/sdX)
  `iscsiadm -m node --targetname "iqn.2012-01.com.nfsec:iscsi.slashboot.caisson" --portal "10.0.0.1:3260" --logout`

### Dealing with existing LVM volumes locally on the fileserver ###

1. Create /dev/loop0 pointing to a logical volume acting as a disk drive (i.e., it has a partition table and MBR)
  `losetup /dev/loop0 /dev/vg0/lucid_rootfs`
+ Map all partitions on /dev/loop0 (make the kernel aware of them)
  `kpartx -av /dev/loop0`
+ Mount the first partition on /dev/loop0 in /mnt
  `mount /dev/mapper/loop0p1 /mnt`
+ Umount when you're done
  `umount /mnt`
+ Delete the mapped partitions from a loopback device
  `kpartx -dv /dev/loop0`
+ Disconnect a loopback device
  `losetup -d /dev/loop0`

### LVM creation and destruction ###

1. Create a new logical volume in volume group vg0 (will appear as `/dev/vg0/iscsi.slashboot.creeper`)
  `lvcreate -L1G -n iscsi.slashboot.creeper vg0`
+ Delete an existing logical volume (WARNING: causes data loss)
  `lvremove /dev/vg0/lucid-rootfs`

### Important config files on FileServer ###

* `/etc/dhcp/dhcpd.conf`
  Contains DHCP information for all known clients.  Sends them gPXE and then the appropriate files from `http://10.0.0.1/~driver/*.html`
* `/home/driver/public_html/*.html`
  Contains the iSCSI Target from which the appropriate client will attempt to boot (via DHCP settings).
* `/etc/iet/ietd.conf`
  Contains the iSCSI Target definitions.  Each one points to a logical volume in `/dev/vg0`.  We do not currently authenticate anything.  By being physically connected to the internal network, you win.

#### Important config files on Client's root filesystem (`/dev/vg0/lucid_rootfs` on the server) ####

* `/etc/initramfs-tools/modules`
  This tells the `mkinitramfs` tool about additional kernel modules to include.  We need a bunch for iSCSI and one for aufs:
    * iscsi_trgt
    * iscsi_tcp
    * libiscsi_tcp
    * libiscsi
    * scsi_transport_iscsi
    * scsi_mod
    * aufs # Thanks to [aufsRootFileSystemOnUsbFlash](https://help.ubuntu.com/community/aufsRootFileSystemOnUsbFlash)
* `/etc/iscsi/iscsi.initramfs`
  This file helps to notify the scripts that create an initramfs to bring in iSCSI support.  The contents of the file should be a *unique* InitiatorName.  Note that we currently *violate* this and get away with it, since we override it on the Linux kernel command line (when driving grub over the serial interface; there is no `menu.lst`).
* `/etc/iscsi/nodes/*`
  These files describe the iSCSI targets that the client ("Initiator") knows about.  Linux will not be able to mount its root filesystem if there's no subdirectory in nodes/ for the iSCSI Target that will serve as the root filesystem (to be distinguished from /boot).  This will manifest as a boot-time hang fairly late in the Linux boot process.  These entries are created automatically by a manual iSCSI discovery:
`iscsiadm -m discovery -t st -p 10.0.0.1`
* `/etc/initramfs-tools/scripts/init-bottom/rootaufs`
  [This little script](https://help.ubuntu.com/community/aufsRootFileSystemOnUsbFlash) teaches the initramfs (and some subsequent initscripts???) what to do with the `aufs=tmpfs` kernel command line option.
* `/etc/init/hostname.conf`
  We want to set the test system's hostname based on the Linux kernel command-line.  That is, grub parameters include `hostname=foo`.  To do this the above-named script should be modified.  In a minimal installation, it may also be necessary to enable the `hostname` "service" by invoking: `update-rc.d hostname defaults`
* `/etc/network/interfaces`
  We need to make sure another DHCP request or other system network startup scripts don't accidentally disrupt the system's connection to the iSCSI server:
  `auto eth0`
  `iface eth0 inet manual`

#### Building the Client's root filesystem ####

After mounting the root filesystem somewhere (e.g., `/mnt`):

    debootstrap --arch i386 maverick $TARGET http://mirror.anl.gov/ubuntu
    mount -o bind /proc $TARGET/proc
    mount -o bind /sys $TARGET/sys
    mount -o bind /dev $TARGET/dev
    LANG= chroot $TARGET
    apt-get install aptitude
    vi /etc/apt/sources.list # add full set of entries, e.g., from existing Ubuntu installation
    aptitude update
    aptitude install build-essential kernel-package libncurses5-dev fakeroot wget bzip2 \
      libncurses5-dev autoconf automake libtool libgtk2.0-dev libssl-dev \
      less minicom vim subversion openssh-server emacs nfs-common \
      nfs-client mercurial rsync traceroute bridge-utils gawk python-dev \
      git-core git-svn gitk libpci-dev bcc bin86 uuid-dev iasl ntpdate \
      acpidump jsvc chromium-browser secure-delete \
      open-iscsi \
      linux-image-XXX \
      grub

#### Explanation of Linux kernel command line options that we use ####


* `root=UUID=e62ba4c2-87d2-4b42-b66d-dabf9af0c68c ro`
   Definitely use UUID for filesystems here; there's no way of knowing how many storage devices are present in an unfamiliar system.
* `ip=dhcp`
   I *think* we need this because of a chicken-and-egg problem with networking and the root filesystem.  This may actually get parsed by the initramfs.
* `hostname=caisson`
   `/etc/init/hostname.conf` with Jon's tweaks reacts to this.
* `ISCSI_INITIATOR=iqn.2012-02.com.nfsec:01:78acc0af8fa7`
   This is the "identity" that the Initiator (Client) will assume in the iSCSI protocol.  It must be unique.  I've been setting the hex after the final colon as the Ethernet MAC address of that client system, to help identify which systems are which. 
* `ISCSI_TARGET_NAME=iqn.2012-01.com.nfsec:lucid_rootfs`
   This is the iSCSI Target that is the root filesystem that will be mounted by the initramfs.  It does not contain anything in /boot.
* `ISCSI_TARGET_IP=10.0.0.1 ISCSI_TARGET_PORT=3260`
   These two options let the iSCSI Initiator logic know which server to talk to, i.e., this is the fileserver's IP and iSCSI port.
* `aufs=tmpfs`
   This tells the initramfs and init-scripts to mount the root filesystem read-only, but to allow writes using aufs http://aufs.sourceforge.net/. I.e., this overlays a ramdisk on the read-only filesystem.  
* `initrd.img-2.6.32.26+drm33.12emhf-jm1`
  This is a typical initramfs, but the important point is that it was regenerated from within the diskless client's filesystem (e.g., a `chroot` environment) AFTER the necessary tweaks (described above) have been made in `/etc/initramfs-tools/`.

Disk image management
---------------------

What different root filesystem images do we want / need? Variables:

* (32-bit, 64-bit)
* (Ubuntu 10.04 LTS with *custom* kernel, Ubuntu 10.04 LTS with *stock* kernel, Windows 7)
* (Do, We, Need, a, Different, Windows, Image, For, Each, Hardware, Platform?)

Recovery
--------

A crashed test system is no problem.  All test runs in `nightly.sh` start by power-cycling the relevant systems (either via Intel AMT or using a remotely controlled outlet attached to squid).
* For systems that support *Intel AMT*, a crashed system can easily be remotely rebooted.
    * Sometimes amttool hangs.  Kill-and-retry support is working within the relevant scripts.
* For systems where no consistent standard exists (AMD systems and perhaps some Intel systems):
    * Seems safe to assume Wake-On-LAN.
    * Desktops/Servers: connect via remotely controllable AC power to power-cycle a crashed system.  Use Wake-On-LAN if it won't auto-power-on.  `aptitude install etherwake; etherwake [mac address]` where MAC address is the ethernet MAC address in the with-colons format, e.g., `etherwake de:ad:be:ef:ca:fe`
    * Laptops: As with desktops, but remove battery so that remotely controllable AC power is effective.
        * This (power-cycle with no battery + WoL using etherwake) is tested and working with an HP ProBook 6555b.

Logging
-------

* Philosophy: Success logs are just as valuable as failure logs, as they form a reference point against which problems / regressions can be compared. Disk is cheap.  No plans to delete logs until we're forced to go there.  Just compress them.
* We would like complete serial output every time, success or failure.  Organize by host ethernet MAC address, tag with relevant metadata (OS version, etc).
* Scraping the logs with scripts to generate some kind of "pretty" presentation of test results is a secondary task, but decisions that would make doing that difficult should be avoided.

Sharing
-------

Ultimately it would be great if folks (e.g., students) without the necessary special hardware setup could submit their own jobs to be run / tested on our test platform.

Serial Settings
---------------

Server `squid` has an 8-port serial adapter card.  The relationship between /dev/ttySn and the number actually printed on the "squiddy" cable is non-obvious:

Cable 1 - /dev/ttyS4
Cable 2 - /dev/ttyS5
Cable 3 - /dev/ttyS6
Cable 4 - /dev/ttyS7
Cable 5 - /dev/ttyS8
Cable 6 - /dev/ttyS9
Cable 7 - /dev/ttyS2
Cable 8 - /dev/ttyS3

For all of these ports to show up the kernel command line also needs to include `8250.nr_uarts=10` (i.e., put it in `/etc/defaults/grub`).
