# test host 'test-e8100' (HP Elite 8100 tower with Intel CPU)

TEST_HOSTNAME=test-e8100
TEST_MACADDR=78:ac:c0:b1:83:aa
TEST_CONNECTION=amtterm
SERIAL_ADDR=0x1188
BOOT_ROOT_UUID=c2a09e3b-08ba-409a-a896-bac38e8a8347

# Setting nr_uarts=0 prevents the Linux kernel from doing any serial
# port initialization.  The serial ports are thus exclusively
# available to the hypervisor and for PAL debug output.  We do this to
# increase the reliability of amtterm.
ADDL_KERNEL_PARAM=8250.nr_uarts=0
