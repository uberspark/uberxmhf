#!/usr/bin/perl
# module.pl: generate module hash value for TrustVisor
# Written for TrustVisor by Ning Qu
#
# input: moduledir [initrd]
# output: std console, usually directed into hashlist.c

if (($#ARGV != 0) && ($#ARGV != 1)) {
	print "usage: module.pl moduledir [intird]\n";
	exit;
}

$path = $ARGV[0];

if ($#ARGV == 1)
{
	# this part is to grab modules in the initrd image
	# it works with Fedora 6, but not tested with the other versions
	$initrd = $ARGV[1];
	$initimage = "intird";
	system("rm -rf /tmp/$initimage; mkdir /tmp/$initimage");
	system("cp $initrd /tmp/$initimage/$initimage.gz -f");
	system("cd /tmp/$initimage; zcat $initimage.gz | cpio -i --quiet");
}

$hostname = `hostname`;
$date = `date`;
print("/* Hostname: $hostname * Path: $path\n * Initrd: $initrd\n * Date: $date */\n");
	
$modfile = "/tmp/modlist";
# get the list of all the modules in the system
if ($#ARGV == 1)
{
	system("find /tmp/$initimage $path | grep \".ko\$\" > $modfile");
}
else
{
	system("find $path | grep \".ko\$\" > $modfile");
}

$secfile = "/tmp/sections";

open(MODLIST, $modfile) or die("can't open module list file!");
while (defined($module=<MODLIST>))
{
	chomp($module);
#	print("$module\n");
	if ($module !~ /ko/)
	{ 
		last;
	}
	# get the sections information of current module
	system("readelf -W -S $module > $secfile.tmp");
	system("grep -e \"\\ \\ \\[\\ \" $secfile.tmp > $secfile.tmp1");
	system("grep -e \"  \\[[0-9]\" $secfile.tmp > $secfile.tmp2");
	# filter the sections with only necessary sections left
	system("grep -e \"X\\ \" -e \"altinstructions\" -e \".rel.text\" -e \".rel.exit.text\" -e \".rel.init.text\" -e \".rel.altinstructi\" $secfile.tmp1 > $secfile.tmp3");
	system("grep -e \"X\\ \" -e \"altinstructions\" -e \".rel.text\" -e \".rel.exit.text\" -e \".rel.init.text\" -e \".rel.altinstructi\" $secfile.tmp2 > $secfile.tmp4");
	# get the offset and size information of these sections
	system("awk '{ print \$6\" \"\$7 }' $secfile.tmp3 > $secfile.hash");
	system("awk '{ print \$5\" \"\$6 }' $secfile.tmp4 >> $secfile.hash");
	
	# get the checksum of the module
	%checksum = system("./sha1 $secfile.hash $module");
	print("$checksum[0]	/* $module */\n");
}

if ($#ARGV == 1)
{
	system("rm -rf $secfile* $modfile /tmp/$initimage");
}else
{
	system("rm -rf $secfile* $modfile");
}
