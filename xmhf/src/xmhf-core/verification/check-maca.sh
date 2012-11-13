#!/bin/bash

# XMHF MAC(a) verification 
# i.e., ensure that NPT structures are always in the data section
# they are supposed to be in

# bail out on any errors
set -e

echo -------------------------------------------------------------------
echo Checking x86svm HPT data structure locations...
echo -------------------------------------------------------------------

