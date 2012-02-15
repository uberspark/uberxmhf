#!/bin/bash

# This script contains a generic bootloader configuration for a
# typical test host.  These variables are sourced from a host-specific
# configuration file that overrides typical values with any needed
# per-host values.

# Values that are actually expected to change across test hosts:
# 1. SINIT module is chipset-dependent on Intel hosts
# 2. ISCSI_INITIATOR should be unique per test host (currently it is 
#    unique because of a suffix containing that test host's ethernet MAC 
#    address)
# 3. hostname= variable (currently ignored by test Linux environment)
# 4. The actual kernel version itself, if we want to test multiple versions
# 5. Whether we need to prefix grub entries with /boot
# 6. Should we be using a serial port or amtterm?
# 7. If serial port, which outlet on the Remote Power Switch controls power?

# All of these variables get set and evaluated before invoking an
# 'expect' script that can handle the interactive session with grub
# via a serial port or amtterm.  Power cycling the test host with (i)
# amtterm or (ii) a hard power cycle using the Remote Power Switch +
# etherwake is also expected to be performed.

if [ -z $1 ]; then
    echo "Usage: $0 [test hostname]"
    echo "       Define environment variable DRYRUN=echo to get a dry-run"
    echo "       of the commands that would be executed."
    exit
fi

SERIAL_BAUD=115200
SERIAL_PARITY=8n1
SERIAL_ADDR=0x3f8

TEST_SLASHBOOT=

TEST_KERNEL=vmlinuz-3.0.4-jm2
TEST_INITRD=initrd.img-3.0.4-jm2
TEST_SINIT=i5_i7_DUAL_SINIT_18.BIN

TEST_ROOT_UUID=ad60f8ff-e0ca-4294-a7d4-9c07da18365b
BOOT_ROOT_UUID=ad60f8ff-e0ca-4294-a7d4-9c07da18365b
TEST_MACADDR=decafebadbad
ISCSI_TARGET_NAME=iqn.2012-01.com.nfsec:oneiric_rootfs
ISCSI_TARGET_IP=10.0.0.1
ISCSI_TARGET_PORT=3260

TEST_HOSTNAME=oneiric

# Options are serial or amtterm
TEST_CONNECTION=serial
# See 8x serial cable number <-> ttySx mapping,
# and test host <-> power outlet mapping, at
# https://plover.pdl.cmu.local/projects/emhf/wiki/Regression_Testing_Ideas
TEST_CONNECTION_SERIAL_PORT=
TEST_CONNECTION_OUTLET_NUMBER=

# Override the above default settings with host-specific settings
CFG_FILENAME=cfg-$1.sh
if [ -e $CFG_FILENAME ]; then
    echo "Sourcing configuration from: $CFG_FILENAME"
else
    echo "ERROR: Configuration file $CFG_FILENAME not found" 1>&2
    exit
fi

. $CFG_FILENAME

if [ $1 != $TEST_HOSTNAME ]; then
    echo "ERROR: inconsistent hostnames: $1 and $TEST_HOSTNAME" 1>&2
    exit
fi

export FIRST_ROOT="root (hd0,0)"
export FIRST_KERNEL="kernel $TEST_SLASHBOOT/init-x86.bin serial=$SERIAL_BAUD,$SERIAL_PARITY,$SERIAL_ADDR"
export FIRST_MOD1="module $TEST_SLASHBOOT/hypervisor-x86.bin.gz"
export FIRST_MOD2="modulenounzip (hd0)+1"
# On an AMD host this is a dummy module and gets ignored
export FIRST_MOD3="module $TEST_SLASHBOOT/$TEST_SINIT"

export SECOND_ROOT="uuid $BOOT_ROOT_UUID"
export SECOND_KERNEL="kernel $TEST_SLASHBOOT/$TEST_KERNEL root=UUID=$TEST_ROOT_UUID ro ip=dhcp hostname=$TEST_HOSTNAME ISCSI_INITIATOR=iqn.2012-02.com.nfsec:01:$TEST_MACADDR ISCSI_TARGET_NAME=$ISCSI_TARGET_NAME ISCSI_TARGET_IP=$ISCSI_TARGET_IP ISCSI_TARGET_PORT=$ISCSI_TARGET_PORT aufs=tmpfs"
export SECOND_MOD1="initrd $TEST_SLASHBOOT/$TEST_INITRD"

export AMT_PASSWORD='AMTp4ssw0rd!'

# echo $FIRST_ROOT
# echo $FIRST_KERNEL
# echo $FIRST_MOD1
# echo $FIRST_MOD2
# echo $FIRST_MOD3
# echo $SECOND_ROOT
# echo $SECOND_KERNEL
# echo $SECOND_MOD1

if [ $TEST_CONNECTION = "serial" ]; then
    # Turn this machine's outlet off (just in case it's on), pause, then turn it on
    echo "Powering off outlet"
    $DRYRUN ./power-control.exp ttyS0 of $TEST_CONNECTION_OUTLET_NUMBER
    $DRYRUN sleep 2
    echo "Powering on outlet"
    $DRYRUN ./power-control.exp ttyS0 on $TEST_CONNECTION_OUTLET_NUMBER

    # If it has been power-cycled then we want to Wake-on-Lan:
    # (and if the machine is already up, this is harmless)
    $DRYRUN sleep 3
    echo "Sending wake-on-LAN packet"
    $DRYRUN etherwake $TEST_MACADDR
fi

if [ $TEST_CONNECTION = "amtterm" ]; then
    echo "Cycling power using amtterm. Powering down."
    echo y | $DRYRUN amttool $TEST_HOSTNAME powerdown
    sleep 1
    echo "Powering up."
    echo y | $DRYRUN amttool $TEST_HOSTNAME powerup
fi

echo "Starting grub-generic.exp"
$DRYRUN ./grub-generic.exp $TEST_CONNECTION $TEST_CONNECTION_SERIAL_PORT
