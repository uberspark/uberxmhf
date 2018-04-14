#/*
# * @XMHF_LICENSE_HEADER_START@
# *
# * eXtensible, Modular Hypervisor Framework (XMHF)
# * Copyright (c) 2009-2012 Carnegie Mellon University
# * Copyright (c) 2010-2012 VDG Inc.
# * All Rights Reserved.
# *
# * Developed by: XMHF Team
# *               Carnegie Mellon University / CyLab
# *               VDG Inc.
# *               http://xmhf.org
# *
# * Redistribution and use in source and binary forms, with or without
# * modification, are permitted provided that the following conditions
# * are met:
# *
# * Redistributions of source code must retain the above copyright
# * notice, this list of conditions and the following disclaimer.
# *
# * Redistributions in binary form must reproduce the above copyright
# * notice, this list of conditions and the following disclaimer in
# * the documentation and/or other materials provided with the
# * distribution.
# *
# * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
# * its contributors may be used to endorse or promote products derived
# * from this software without specific prior written permission.
# *
# * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
# * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
# * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
# * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
# * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
# * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
# * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
# * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
# * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
# * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
# * SUCH DAMAGE.
# *
# * @XMHF_LICENSE_HEADER_END@
# */

# awk program to fiter the output of objdump to include only code sections
# author(s): amit vasudevan (amitvasudevan@acm.org)
#
BEGIN { 
	cur_section_num = 0;
	characteristics_line=0;
	total_entries = 0;
	current_entry = "";
	max_entries=96;
	for(i=1; i <= max_entries; i++)
		entry[i]="";
}
		
{ 
	/* printf("\n%s : %u", $0, cur_section_num); */
	if($1 == cur_section_num){
		cur_section_num++;
		/* section id, section name, section VMA, section size, section file offset*/
		current_entry=$1 ":" $2 ":" $4 ":" $3 ":" $6; 
	}
}

/, CODE/ {
		total_entries++; 
		entry[total_entries]=current_entry;
		/* printf("\ncentry=%s", current_entry); */
}

END {
	for(i=1; i <= total_entries; i++)
		printf("%s\n", entry[i]);
	/*printf("\nDone.");*/
}
