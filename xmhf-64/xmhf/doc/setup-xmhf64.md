# Setting up XMHF64

## Introduction
XMHF64 is branch of XMHF that supports running XMHF in both 32-bit and 64-bit.
32-bit is called "i386" and 64-bit is called "amd64". This bit width difference
is called "subarch".

XMHF has 3 phases: bootloader, secureloader, and runtime. Bootloader will
always run in i386. Secureloader and runtime will run in the subarch as
configured by the user (i386 or amd64). Only amd64 XMHF can run amd64 guest
operating systems. A comparision is below.

| Name             | XMHF in i386  | XMHF in amd64           |
|------------------|---------------|-------------------------|
| bootloader       | i386          | i386                    |
| secureloader     | i386          | amd64                   |
| runtime          | i386          | amd64                   |
| guest OS         | i386 (no PAE) | i386 or amd64           |
| physical memory  | 4 GiB         | >= 4 GiB (configurable) |

## Support status

This section documents supported software and hardware of XMHF64

### Hardware
Real CPUs
* Intel: supported.
	* CPUs newer than Haswell have not been tested.
* AMD: not supported.

Hypervisors
* QEMU / KVM: supported for Intel CPU, require `--enable-kvm` and `vmx` flag in
  the CPU.
* VMWare: probably supported.

### Software
In principle, any guest operating system should work, as long as it:
* Uses 32-bit paging / PAE paging / 4-level paging (5-level paging not
  supported).
* Does not require hardware virtualization features, does not require TPM.

The following OS are known to work:
* Ubuntu 12.04 LTS
* Debian 11 with kernel 5.10.0-9
* Fedora 35
* Windows XP
* Windows 7
* Windows 8.1
* Windows 10

## Compiling XMHF

Compiling XMHF64 is tested on Debian 11 and Fedora 35. For Ubuntu, the usage
should be similar to Debian. For Docker, the `debian:11` tag is tested. This
documentation will use "Debian" and "Fedora" to differentiate between RPM-based
Linux and DEB-based Linux.

### Installing build tools

* When building i386 XMHF on i386 Debian, just install build essentials
	```sh
	apt-get update
	apt-get install build-essential
	```
* When building i386 XMHF on amd64 Debian, also install cross build packages
  (this configuration is currently not tested extensively)
	```sh
	apt-get update
	apt-get install build-essential crossbuild-essential-amd64
	```
* When building on amd64 Debian, cross build for i386 is always needed, because
  bootloader is in i386. Install dependencies with:
	```sh
	apt-get update
	apt-get install build-essential crossbuild-essential-i386
	```
* When building on amd64 Fedora (looks like as of Fedora 35 there is no support
  for i386 Fedora), install dependencies with:
	```sh
	dnf install autoconf automake make gcc
	# The next line installs fallocate, which is recommended
	dnf install util-linux
	```

### Building

Building XMHF contains 3 steps: autogen, configure, and make.

#### 1. Autogen
In xmhf64 project root directory, first run autogen:
```sh
./autogen.sh
```

#### 2. Configure
Then run configure. Configure selects hypapp and build subarch etc.

`.github/build.sh` can be used to generate configuration options. It can be
especially helpful to figure out cross-compile options. See comments at the
start of this file. Try the following:
```sh
./.github/build.sh i386 release -n
./.github/build.sh amd64 release -n
```

If not using `.github/build.sh`, the usage of configure is
```sh
./configure --with-approot=HYPAPP [ARGUMENTS [...]]
```

Mandatory arguments
* `--with-approot=HYPAPP`: HYPAPP is the relative path to hypapp. For example,
  building TrustVisor should be `--with-approot=hypapps/trustvisor`
* `--with-target-subarch=...`: Depending on cross build situations, add these
  **mandatory** extra arguments to specify subarch of XMHF to build
	* Build i386 XMHF on i386 (Debian / Fedora): (no extra arguments)
	* Build amd64 XMHF on i386 ...
		* ... Debian:
		  `--with-target-subarch=amd64 CC=x86_64-linux-gnu-gcc LD=x86_64-linux-gnu-ld`
		* ... Fedora:
		  `--with-target-subarch=amd64`
	* Build i386 XMHF on amd64 ...:
		* ... Debian:
		  `CC=i686-linux-gnu-gcc LD=i686-linux-gnu-ld`
		* ... Fedora: (no extra arguments)
	* Build amd64 XMHF on amd64 (Debian / Fedora):
	  `--with-target-subarch=amd64`
	* If these argument is not added correctly, an error message like
	  `ld: cannot find -lgcc` may appear when building.

Recommended arguments
* The following arguments helps debugging and are highly recommended. They have
  minimum impact on XMHF's behavior.
	* `--enable-debug-symbols`: add debug info to generated ELF files. With
	  this configuration, GDB can print symbols in `*.exe` files.
	* `--enable-debug-qemu`: allow XMHF to run in QEMU (disables some unused
	  VMCS fields)
* The following arguments disables certain functionalities.
	* `--disable-drt`: disable Dynamic Root of Trust (e.g. uses Intel TXT)
	* `--disable-dmap`: disable DMA protection (e.g. uses Intel VT-d)
* `--with-amd64-max-phys-addr`: configure physical address supported by amd64
  XMHF.
	* For example, `--with-amd64-max-phys-addr=0x140000000` sets physical
	  address to 5 GiB. The default is 16 GiB. When XMHF runs on a machine that
	  has more physical memory than this value, XMHF will halt. This
	  configuration is ignored in i386 XMHF.

Other arguments
* `--disable-debug-serial --enable-debug-vga`: print debug messages on VGA, not
  serial port.
* `--with-opt=<COMPILER FLAGS>`: compile XMHF with optimization. For example,
  `--with-opt='-O3 -Wno-stringop-overflow'` adds `-O3` and
  `-Wno-stringop-overflow` to GCC's arguments to compile in optimization `-O3`.
  As of writing of this documentation, `-Wno-stringop-overflow` is needed due
  to a bug in GCC: <https://gcc.gnu.org/bugzilla/show_bug.cgi?id=105100>
* `--enable-optimize-nested-virt`: enable some risky optimizations in intercept
  handling.
	* When running XMHF under many levels of nested virtualization, VMREAD and
	  VMWRITE instructions become expensive. This configuration enables
	  manually optimized intercept handling for some cases to prevent XMHF from
	  running too slow to boot the guest OS. However, these optimizations need
	  to be manually maintained and may be incorrect.

#### 3. Make
After configuring, simply run Make.
```sh
make
```

To use multiple processors on the compiling machine, try `make -j $(nproc)`.

#### Build results
After building successfully, there should be two files, where `$(SUBARCH)` is
`i386` or `amd64`:
```
init-x86-$(SUBARCH).bin
hypervisor-x86-$(SUBARCH).bin.gz
```

#### Configuration examples

```sh
# Build i386 XMHF on i386 Ubuntu, without DRT and DMAP
./configure --with-approot=hypapps/trustvisor --disable-dmap --disable-drt

# Build i386 on amd64 Debian
./configure --with-approot=hypapps/trustvisor --enable-debug-symbols --enable-debug-qemu CC=i686-linux-gnu-gcc LD=i686-linux-gnu-ld

# Build amd64 on amd64 Debian, with 8 GiB memory, and use VGA instead of serial
./configure --with-approot=hypapps/trustvisor --with-target-subarch=amd64 --enable-debug-symbols --enable-debug-qemu --with-amd64-max-phys-addr=0x200000000 --disable-debug-serial --enable-debug-vga
```

## Installing XMHF

Copy these files to `/boot/` of the operating system. These files will be
accessed by GRUB.
```
init-x86-$(SUBARCH).bin
hypervisor-x86-$(SUBARCH).bin.gz
```

## Booting XMHF

### Theory
GRUB 2 needs to be installed to run XMHF64. GRUB 2 will be used to launch
XMHF64 and to launch the guest operating system. This usually requires the user
to select different menu entries in GRUB.

GRUB 2 needs to be launched by BIOS. EFI / UEFI is not supported. This means
that XMHF likely does not work on disks formatted as GPT (XMHF works on MBR).

The boot sequence is:
1. The machine starts, BIOS starts running
2. BIOS launches GRUB
3. GRUB launches XMHF64
4. XMHF64 launches GRUB in virtual machine mode (e.g. Intel VMX)
5. GRUB launches guest OS

### Configuration
A menuentry needs to be added to GRUB. For Debian it is done by adding a file
with execute permission in `/etc/grub.d/`. For example, create a file at
`/etc/grub.d/42_xmhf_i386`:

```sh
#!/bin/sh
exec tail -n +3 $0
# This file provides an easy way to add custom menu entries.  Simply type the
# menu entries you want to add after this comment.  Be careful not to change
# the 'exec tail' line above.

menuentry "XMHF-i386" {
	set root='(hd0,msdos1)'		# point to file system for /
	set kernel='/boot/init-x86-i386.bin'
	set boot_drive='0x80'	# should point to where grub is installed
	echo "Loading ${kernel}..."
	multiboot ${kernel} serial=115200,8n1,0x5080 boot_drive=${boot_drive}
	module /boot/hypervisor-x86-i386.bin.gz
	module --nounzip (hd0)+1	# should point to where grub is installed
	module /boot/i5_i7_DUAL_SINIT_51.BIN
}
```

Please following the line by line explanation of the file above to edit it
* `#!/bin/sh` and `exec tail -n +3 $0`: this executable file will print the
  content starting at line 3. Don't touch them.
* `menuentry "XMHF-i386" {`: "XMHF-i386" will be the entry name in GRUB. This
  name can be changed freely.
* `set root='(hd0,msdos1)'`: set partition of the operating system. This
  partition is used to access XMHF files. `(hd0,msdos1)` is first disk's first
  MBR partition. See GRUB's documentation.
* `set kernel='/boot/init-x86-i386.bin'`: set XMHF bootloader file. Change
  `init-x86-i386.bin` to `init-x86-amd64.bin` for amd64 XMHF.
	* In the example configuration, GRUB should find a MBR partition on the
	  first hard drive (hd0). The partition should contain a file system with a
	  directory called `boot` at the root, and this directory should contain
	  the file `init-x86-i386.bin`.
* `set boot_drive='0x80'`: specify the disk where XMHF can find GRUB. `0x80` is
  the first hard disk (corresponding to `hd0`), `0x81` is the second hard disk
  (`hd1`), etc. Usually this does not need to change if you are only working
  with only one hard disk.
* `echo "Loading ${kernel}..."`: just printing a message, no need to change
* `multiboot ${kernel} serial=115200,8n1,0x5080 boot_drive=${boot_drive}`:
  specify multiboot kernel to be the XMHF bootloader
	* `serial=115200,8n1,0x5080`: specify serial parameters. The parameters can
	  usually be found by running `dmesg | grep ttyS`. For example you may see
	  `... ttyS0 at I/O 0x5080 (irq = 17, base_baud = 115200) is a 16550A`.
* `module /boot/hypervisor-x86-i386.bin.gz`: load the first multiboot module,
  which must be XMHF secureloader and runtime. Again change it to
  `hypervisor-x86-amd64.bin.gz` if running amd64 XMHF.
* `module --nounzip (hd0)+1`: specify the disk where XMHF can find GRUB.
  `(hd0)` is the first hard disk, and `+1` means 1 block since offset 0
  (this is GRUB's block list syntax). Usually this does not need to change if
  you are only working with only one hard disk.
* `module /boot/i5_i7_DUAL_SINIT_51.BIN`: For a Intel machine with DRT enabled,
  this is the SINIT AC Module downloaded from Intel's website:
  <http://software.intel.com/en-us/articles/intel-trusted-execution-technology/>.
  Make sure to select the file that matches your machine's CPU. When DRT is
  disabled, can remove this line.

After the modification is done, make it executable and update GRUB.
```sh
chmod +x /etc/grub.d/42_xmhf_i386
update-grub
```

#### Multiple disks

It may be convenient to install GRUB on one disk and the guest operating system
on another. Consider this scenario: we have installed XMHF on a USB, and we
want to test it on an OS installed on a HDD.

The partition table of USB looks like:
```
+------------+---------------------------------------------+
| MBR header | Partition 1: ext4                           |
+------------+---------------------------------------------+
| GRUB       | XMHF installed in /boot/                    |
+------------+---------------------------------------------+
```

The partition table of HDD looks like:
```
+------------+-----------------------+---------------------+
| MBR header | Partition 1: ???      | Partition 2: ???    |
+------------+-----------------------+---------------------+
| Bootloader | Guest OS              | ...                 |
+------------+-----------------------+---------------------+
```

The target computer by default only has the HDD connected. When a BIOS boots
the HDD, it will set DL=0x80, and `(hd0)` is HDD. When a USB is inserted, the
USB is `(hd1)`.

However, if the BIOS boots the USB, then the USB becomes `(hd0)` and the HDD
becomes `(hd1)`. The BIOS will still set DL=0x80.

Suppose we want to make the boot sequence "BIOS -> USB GRUB -> XMHF -> HDD
Bootloader". Then USB GRUB should find the HDD Bootloader at `(hd1)`, and HDD
bootloader should be passed DL=0x81. So the configuration file should be

```
#!/bin/sh
...
menuentry "XMHF-i386" {
	...
	set boot_drive='0x81'
	...
	module --nounzip (hd1)+1
	...
}
```

## Configuring BIOS

This section has not been tested extensively. For Intel, the idea is to turn on
virtualization, VT-d, TPM, and TXT. Please see XMHF documentations.

## Running XMHF

First start / restart the target machine. When the first time GRUB is seen,
select the menuentry for XMHF. Then after sometime GRUB will be seen the second
time. At that time select menuentry to boot the guest OS.

