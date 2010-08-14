#!/usr/bin/perl

if ($#ARGV < 0)
{
	print "usage: visor.pl visor_image\n";
	exit;
}

$hostname = `hostname`;
$date = `date`;
print("/* Hostname: $hostname * Date: $date */\n");
$image = "TrustVisor";
system("rm -f /tmp/$image* &> /dev/null");

$visor = $ARGV[0];
# ignore init area in the raw image
$off = 0x200000;
# copy the runtime TrustVisor image
system("dd if=$visor of=/tmp/$image bs=1 skip=$off 2>/dev/null");
$size = `ls -l /tmp/$image | awk '{print \$5}'`;
chomp($size);
%checksum = system("./sha1 /tmp/$image");
print("$checksum[0]	/* $visor (offset: $off, size: $size) */\n");

system("rm -f /tmp/$image*");
