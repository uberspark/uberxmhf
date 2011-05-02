#!/bin/bash

# See README for a more detailed explanation.

if [ ! -e ./seal-code ] ; then
    echo "You need to 'make' first!"
fi

echo "************************************************"
echo Sealing secret-fun.bin:
echo "************************************************"
./seal-code secret-fun.bin secret-fun.bin.sealed

echo "************************************************"
echo Running the sealed code:
echo "************************************************"
./load-code secret-fun.bin.sealed "input data"

echo "************************************************"
echo Tampering with the sealed code
echo "************************************************"
echo "tampering" >> secret-fun.bin.sealed
./load-code secret-fun.bin.sealed "input data"
  
