#!/usr/bin/perl -w

$push = 0;

while(<STDIN>) {

    if ($push) {
	print;
	if (/.*\)\;/) {
	    #print "End multiline inline assembly:\n\n";
	    print "*/\n";
	    $push = 0;
	}
    } else {
	if (/\s*asm.*\;/) {
	    #print "Begin single line inline assembly:\n";
	    print "// $_";
	} elsif (/\s*asm.*/) {
	    #print "Begin multiline inline assembly:\n";
	    print "/* $_";
	    $push = 1;
	} else {
	    # not inline assembly
	    print;
	}
    }
}
