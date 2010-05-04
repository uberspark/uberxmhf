#!/usr/bin/perl -w

#
#  $Id: size_to_csv_org.pl 1 2008-04-12 19:52:33Z jcw $
#  $Revision: 1 $
#  $Author: jcw $
#  $Date: 2008-04-12 15:52:33 -0400 (Sat, 12 Apr 2008) $
#  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/size_to_csv_org.pl $
#

use strict;

#
#  Set to non-0 to keep columns that are not .comment or .debug*
#
my $useful_columns_only = 1;

{
  my %weight = ('.text'          => 1,
                '.data'          => 2,
                '.str'           => 3,
                '.rodata'        => 4,
                '.rodata.str1.4' => 5,
                '.bss'           => 6,
                'default'        => 7,
               );
  my $line = 0;
  my $state = 0;
  my $filename;
  my %hash_by_filename;
  my %hash_by_section;

  while (<>)
  {
    ++$line;

    if ($state == 0)
    {
      if (/:$/)
      {
        ($filename) = split /\s+/;
        $state = 1;
      }
    }
    elsif ($state == 1)
    {
      if (!/^section/)
      {
        print "Next line is not header\n";
        exit;
      }

      $state = 2;
    }
    elsif ($state == 2)
    {
      if (/^Total/)
      {
        $state = 0;
      }
      elsif (!$useful_columns_only || (!/^\.comment/ && !/^\.debug.*/))
      {
        my ($section, $value) = split /\s+/;
        my $weight = $weight {$section} || $weight {default};

        $hash_by_filename {$filename}{$section} = {weight => $weight, value => $value};
        $hash_by_section {$section} = $weight;
      }
    }
  }

  foreach my $fn (keys %hash_by_filename)
  {
    foreach my $section (keys %hash_by_section)
    {
      $hash_by_filename {$fn}{$section} = {weight => $weight{default}, value => 0} if !exists $hash_by_filename {$fn}{$section};
    }
  }

  print "file,", join ",", ( sort by_weight keys %hash_by_section ), "\n";

  sub by_weight { $hash_by_section {$a} <=> $hash_by_section {$b} ||  $a cmp $b }

  foreach my $fn (sort keys %hash_by_filename)
  {
    print $fn, ",", join (",", map {$hash_by_filename {$fn}{$_}{value}} sort by_weight keys %{$hash_by_filename {$fn}}), "\n";
  }
}
