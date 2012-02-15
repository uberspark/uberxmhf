#!/bin/bash

# test host 'girder' (HP ProBook 6555b laptop with AMD CPU)

TEST_SLASHBOOT=/boot
TEST_HOSTNAME=test-6555b
TEST_MACADDR=64:31:50:80:40:b8

# See 8x serial cable number <-> ttySx mapping,
# and test host <-> power outlet mapping, at
# https://plover.pdl.cmu.local/projects/emhf/wiki/Regression_Testing_Ideas
TEST_CONNECTION_SERIAL_PORT=ttyS5
TEST_CONNECTION_OUTLET_NUMBER=2

# # This machine is plugged into port 2 of the StarTech device.
# # Turn its outlet off (just in case it's on), wait 1 second, then turn it on
# echo "Powering off outlet"
# ./power-control.exp ttyS0 of $TEST_CONNECTION_OUTLET_NUMBER
# sleep 2
# echo "Powering on outlet"
# ./power-control.exp ttyS0 on $TEST_CONNECTION_OUTLET_NUMBER

# # If it has been power-cycled then we want to Wake-on-Lan:
# # (and actually, if the machine is already up, this is harmless)
# echo "Sending wake-on-LAN packet"
# sleep 3
# etherwake $TEST_MACADDR

# echo "Starting grub-generic.exp"
# ./grub-generic.exp $TEST_CONNECTION $TEST_CONNECTION_SERIAL_PORT

