#!/usr/bin/perl

# copies loader and runtime to /mnt/mbrgrub/

print "Copying loader.bin...";
system "rm -rf /mnt/mbrgrub/ldn_loader.bin";
system "cp loader.bin /mnt/mbrgrub/ldn_loader.bin";
print "Done.\n";
print "Copying runtime.bin.gz...";
system "rm -rf /mnt/mbrgrub/ldn_runtime.bin.gz";
system "cp runtime.bin.gz /mnt/mbrgrub/ldn_runtime.bin.gz";
print "Done.\n";



