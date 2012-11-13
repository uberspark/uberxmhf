#!/bin/bash

# XMHF MAC(a) verification 
# i.e., ensure that NPT structures are always in the data section
# they are supposed to be in
# author: amit vasudevan (amitvasudevan@acm.org)

# bail out on any errors
set -e

echo -------------------------------------------------------------------
echo Checking x86svm HPT data structure locations...
echo -------------------------------------------------------------------

pdpt_success=$(objdump --syms ../components/xmhf-runtime/runtime.exe | awk '{print $4,$6}' | grep ".palign_data g_svm_npt_pdpt_buffers" | wc -l)
pdts_success=$(objdump --syms ../components/xmhf-runtime/runtime.exe | awk '{print $4,$6}' | grep ".palign_data g_svm_npt_pdts_buffers" | wc -l)
pts_success=$(objdump --syms ../components/xmhf-runtime/runtime.exe | awk '{print $4,$6}' | grep ".palign_data g_svm_npt_pts_buffers" | wc -l)

# echo Return value: $pdpt_success, $pdts_success, $pts_success

if [ $pdpt_success -eq 1 ] && [ $pdts_success -eq 1 ] && [ $pts_success -eq 1 ]
then
	echo "VERIFICATION SUCCESS: NPT data structures are where they should be in the executable!"
	# success
	exit 0
else
	echo "VERIFICATION FAIL: NPT data structures are not in the required section!"
	# fail
	exit 1
fi 

