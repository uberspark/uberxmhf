#!/bin/bash

# if tpm_infineon is loaded, unload it
if [ `lsmod | grep tpm_infineon | wc -l` -ge 1 ]; then
    echo "Unloading Infineon driver; should be using tpm_tis instead"
    modprobe -r tpm_infineon || exit 1
fi

# We want to use tpm_tis
if [ `lsmod | grep tpm_tis | wc -l` = "0" ]; then
    echo -n "Module tpm_tis not loaded; attempting to load... "
    modprobe tpm_tis || exit 2
    echo "Ok."
fi

# Make sure tcsd and tpm-tools are installed
if [ `which tcsd | wc -l` = "0" -o `which tpm_version | wc -l` = "0" ]; then
    echo "tcsd or tpm_version not found. Do you need to:"
    echo "    aptitude install libtspi-dev libtspi1 trousers tpm-tools"
    exit 3
fi

# Make sure tcsd is running
if [ `ps -ef | grep tcsd | grep -v grep | wc -l` = "0" ]; then
    tcsd || exit 4
fi

# Test the TPM by invoking the tpm_version command
tpm_version > /dev/null
if [ $? -ne 0 ]; then
    echo "tpm_version failed unexpectedly; there is something wrong with your TPM."
    exit 5
fi

echo "tpm_tis loaded, tcsd running, and TPM is responsive; we are okay"
exit 0

