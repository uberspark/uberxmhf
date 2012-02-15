# This script should be sourced by another script
# It should not actually be run on its own

SERIAL_BAUD=115200
SERIAL_PARITY=8n1
SERIAL_ADDR=0x3f8

TEST_SLASHBOOT=

TEST_KERNEL=vmlinux-3.0.4-jm2
TEST_INITRD=initrd.img-3.0.4-jm2
TEST_SINIT=i5_i7_DUAL_SINIT_18.BIN

TEST_ROOT_UUID= d60f8ff-e0ca-4294-a7d4-9c07da18365b
TEST_MACADDR=decafebadbad
ISCSI_TARGET_NAME=iqn.2012-01.com.nfsec:oneiric_rootfs
ISCSI_TARGET_IP=10.0.0.1
ISCSI_TARGET_PORT=3260

TEST_HOSTNAME=oneiric

# options are serial or amtterm
TEST_CONNECTION=serial

export FIRST_ROOT='root (hd0,0)'
export FIRST_KERNEL='kernel $TEST_SLASHBOOT/init-x86.bin serial=$SERIAL_BAUD,$SERIAL_PARITY,$SERIAL_ADDR'
export FIRST_MOD1='module $TEST_SLASHBOOT/hypervisor-x86.bin.gz'
export FIRST_MOD2='modulenounzip (hd0)+1'
# On an AMD host such as girder this is a dummy module and is not used
export FIRST_MOD3='module $TEST_SLASHBOOT/$TEST_SINIT'

export SECOND_ROOT='uuid ad60f8ff-e0ca-4294-a7d4-9c07da18365b'
export SECOND_KERNEL='kernel $TEST_SLASHBOOT/$TEST_KERNEL root=UUID=$TEST_ROOT_UUID ro ip=dhcp hostname=$TEST_HOSTNAME ISCSI_INITIATOR=iqn.2012-02.com.nfsec:01:$TEST_MACADDR ISCSI_TARGET_NAME=$ISCSI_TARGET_NAME ISCSI_TARGET_IP=$ISCSI_TARGET_IP ISCSI_TARGET_PORT=$ISCSI_TARGET_PORT aufs=tmpfs'
export SECOND_MOD1='initrd $TEST_SLASHBOOT/$TEST_INITRD'
