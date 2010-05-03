#!/usr/bin/perl

# copies loader and runtime to /mnt/mbrgrub/

print "Copying loader.bin...";
# system "rm -rf /mnt/mbrgrub/loader.bin";
# system "cp loader.bin /mnt/mbrgrub/.";
system "rm -rf /boot/loader.bin";
system "cp loader.bin /boot/loader.bin";
print "Done.\n";
print "Copying runtime.bin.gz...";
# system "rm -rf /mnt/mbrgrub/runtime.bin.gz";
# system "cp runtime.bin.gz /mnt/mbrgrub/.";
system "rm -rf /boot/runtime.bin.gz";
system "cp runtime.bin.gz /boot/runtime.bin.gz";
print "Done.\n";



