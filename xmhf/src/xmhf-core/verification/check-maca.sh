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
svm_success=0;

if [ $pdpt_success -eq 1 ] && [ $pdts_success -eq 1 ] && [ $pts_success -eq 1 ]
then
	svm_success=1
else
	svm_success=0;
fi

echo -------------------------------------------------------------------
echo Checking x86vmx HPT data structure locations...
echo -------------------------------------------------------------------

vmx_pml4_success=$(objdump --syms ../components/xmhf-runtime/runtime.exe | awk '{print $4,$6}' | grep ".palign_data g_vmx_ept_pml4_table_buffers" | wc -l)
vmx_pdpt_success=$(objdump --syms ../components/xmhf-runtime/runtime.exe | awk '{print $4,$6}' | grep ".palign_data g_vmx_ept_pdp_table_buffers" | wc -l)
vmx_pdt_success=$(objdump --syms ../components/xmhf-runtime/runtime.exe | awk '{print $4,$6}' | grep ".palign_data g_vmx_ept_pd_table_buffers" | wc -l)
vmx_pt_success=$(objdump --syms ../components/xmhf-runtime/runtime.exe | awk '{print $4,$6}' | grep ".palign_data g_vmx_ept_p_table_buffers" | wc -l)

vmx_success=0;

if [ $vmx_pml4_success -eq 1 ] && [ $vmx_pdpt_success -eq 1 ] && [ $vmx_pdt_success -eq 1 ] && [ $vmx_pt_success -eq 1 ]
then
	vmx_success=1
else
	vmx_success=0;
fi


echo -------------------------------------------------------------------
echo Checking DMA data structure location...
echo -------------------------------------------------------------------

dma_success=$(objdump --syms ../components/xmhf-runtime/runtime.exe | awk '{print $4,$6}' | grep ".palign_data g_rntm_dmaprot_buffer" | wc -l)


if [ $svm_success -eq 1 ] && [ $vmx_success -eq 1 ] && [ $dma_success -eq 1 ]
then
	echo "VERIFICATION SUCCESS: NPT/EPT and DMA data structures are where they should be in the executable!"
	# success
	exit 0
else
	echo "VERIFICATION FAIL: NPT/EPT and/or DMA data structures are not in the required section!"
	# fail
	exit 1
fi 

