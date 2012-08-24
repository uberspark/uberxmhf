# test host 'test-e8100' (HP Elite 8100 tower with Intel CPU)

ADDL_KERNEL_PARAM=
TEST_HOSTNAME=test-e8100
TEST_MACADDR=78:ac:c0:b1:83:aa
TEST_SLASHBOOT=
TEST_CONNECTION=amtterm
TEST_CONNECTION_OUTLET_NUMBER=
TEST_CONNECTION_SERIAL_PORT=
SERIAL_ADDR=0x1188
BOOT_ROOT_UUID="uuid 7e96bc42-ee24-11e1-8235-b499baa930d4"
#BOOT_ROOT_UUID="uuid c2a09e3b-08ba-409a-a896-bac38e8a8347"

# The nr_uarts=0 work-around below is DISABLED because
# grub-generic.exp has been taught how to detect the death of amtterm
# and automatically restart it.

# Setting nr_uarts=0 prevents the Linux kernel from doing any serial
# port initialization.  The serial ports are thus exclusively
# available to the hypervisor and for PAL debug output.  We do this to
# increase the reliability of amtterm.
#ADDL_KERNEL_PARAM=8250.nr_uarts=0
