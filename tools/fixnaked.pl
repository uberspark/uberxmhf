#!/usr/bin/perl
# script to ensure that naked functions are truly naked without extraneous prologue/epilogue
# will be defunct once but #18791 is fixed in clang (http://llvm.org/bugs/show_bug.cgi?id=18791)
# idea is to operate on the LLVM IR ;)
# author: amit vasudevan (amitvasudevan@acm.org)

use Tie::File;

chomp(my $filename = $ARGV[0]);
tie my @array, 'Tie::File', $filename or die $!;

my $i = 0;

while( $i <= $#array) {
   my $line = $array[$i];
   chomp($line);
   
   if($line eq "; Function Attrs: naked noinline nounwind") {
	#print "$line\n";
	
	#go to the next line and check for the presence of a define
		$i = $i + 1;
		if ($i > $#array){
			print "unexpected end of file!";
			exit 1;
		}
		$line = $array[$i];
		chomp($line);
		if( !($line =~ /^define/) ){
			print "expected define, but could not find it!";
			exit 1;
		}
		
    #ok we found a define, so skip that line 
    #print "$line\n";
	$i = $i + 1;
	if ($i > $#array){
		print "unexpected end of file!";
		exit 1;
	}
	$line = $array[$i];
	chomp($line);
    
    # move on until the next closing }
	my $trimline = $line;
	$trimline =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace
	
	while($trimline ne "}"){
		if(  !( ($trimline =~ /^call /) || ($trimline =~ /^ret/) ) ){
			#$line = ";$line";
			$array[$i] = ";$line";
		}
		if ($trimline =~ /^ret i32/){
			#$line = "ret i32 0";
			$array[$i] = "ret i32 0";
		}
		if ($trimline =~ /^ret i64/){
			#$line = "ret i64 0";
			$array[$i] = "ret i64 0";
		}
		#print "$line\n";
	
		$i = $i + 1;
		if ($i >= $#array){
			print "unexpected end of file!";
			exit 1;
		}
		$line = $array[$i];
		chomp($line);
		$trimline = $line;
		$trimline =~ s/^\s+|\s+$//g ;     # remove both leading and trailing whitespace
	}

	#print "$line\n";
	
   }else{
	   #print "$line\n";
   }

	$i = $i +1;
}


