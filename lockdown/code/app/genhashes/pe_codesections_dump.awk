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
