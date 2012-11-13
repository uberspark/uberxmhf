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
 

