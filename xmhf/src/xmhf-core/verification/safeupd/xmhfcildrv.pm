# 
# XMHF cil driver perl module 
# extends the Cilly module to add high-level pre/post cil/compile hooks
#
# author: amit vasudevan (amitvasudevan@acm.org)
#

package xmhfcildrv;

use strict;
use App::Cilly;

our @ISA = qw(App::Cilly);

sub new {
    my ($proto, @args) = @_;
    my $class = ref($proto) || $proto;
    my $bin;
    my $lib;
    
    $bin = "$::xmhfcildrvhome";
    $lib = "$::xmhfcildrvhome";
    $xmhfcildrv::compiler = "$bin/xmhfcil.exe";
    
    printf "\nBinary directory: %s", $bin;

	my $self;

	if(@args){
		$self = xmhfcildrv->App::Cilly::new(@args);
	}else{
		push @{args}, "--help";
		$self = xmhfcildrv->App::Cilly::new(@args);
	}
		
    # new variables for xmhfcildrv
    $self->{COMPILER} = $xmhfcildrv::compiler;
    printf "\nCompiler: %s", $self->{COMPILER};

    $self->{LIBBASE} = $lib;

    # override Cilly's default
    $self->{SEPARATE} = 1;

    bless $self, $class;
}

#-----------------------------------------------------------------------

sub CillyCommand {
    my ($self, $ppsrc, $dest) = @_;

    my @cmd = ($self->{COMPILER});
    my $aftercil = $self->cilOutputFile($dest, 'cil.c');
    return ($aftercil, @cmd, '--out', $aftercil);
}


#-----------------------------------------------------------------------
# command-line argument processing hooks
sub processArguments {
    my ($self) = @_;
    my @args = @{$self->{ARGV}};

    # Scan and process the arguments
    $self->setDefaultArguments;
    $self->collectArgumentList(@args);

    return $self;
}

sub setDefaultArguments {
    my ($self) = @_;
    return $self->SUPER::setDefaultArguments;
}

sub collectOneArgument {
    my ($self, $arg, $pargs) = @_;
    my $res = 1;
    if ($self->compilerArgument($self->{OPTIONS}, $arg, $pargs)) {
        # this would be a compiler argument so do nothing
        # printf "\ncompilerArgument: %s, operation=%s", $arg, $self->{OPERATION};
    } elsif ($arg eq "--help" || $arg eq "-help") {
        $self->printHelp();
        exit 0;
    } elsif ($arg =~ m|--save-temps=(.+)$|) {
        if (!-d $1) {
            die "Cannot find directory $1";
        }
        $self->{SAVE_TEMPS} = $1;
    } elsif ($arg eq '--save-temps') {
        $self->{SAVE_TEMPS} = '.';
    } elsif ($arg eq '--merge') {
        $self->{SEPARATE} = 0;
    } elsif ($arg =~ m|^--out=(\S+)$|) {
        # Intercept the --out argument
        $self->{CILLY_OUT} = $1;
        push @{$self->{CILARGS}}, "--out", $1;
    } elsif ($arg =~ m|^--|) {
        # All other arguments starting with -- are passed to CIL
        # Split the ==
        if ($arg =~ m|^(--\S+)=(.+)$|) {
            push @{$self->{CILARGS}}, $1, $2;
        } else {
            push @{$self->{CILARGS}}, $arg;
        }
    } else {
        # something that we don't understand, so fail!
        $res = 0;
    }
    return $res;
}



#-----------------------------------------------------------------------
# pre-processing hooks
# we don't implement any of these hooks currently

sub preprocess_before_cil {
    my($self, $src, $dest, $ppargs) = @_;
    my @args = @{$ppargs};
    return $self->SUPER::preprocess_before_cil($src, $dest, \@args);
}

sub preprocessAfterOutputFile {
    my ($self, $src) = @_;
    return $src; 
}

sub preprocess_after_cil {
    my ($self, $src, $dest, $ppargs) = @_;
    return $dest;
}

#-----------------------------------------------------------------------
# compilation hook (e.g., adding your own include directories before
# compilation)
# we don't implement this currently
sub compile_cil {
    my ($self, $src, $dest, $ppargs, $ccargs) = @_;
    my @args = @{$ppargs};
    return $self->SUPER::compile_cil($src, $dest, \@args, $ccargs);
}


#-----------------------------------------------------------------------
# linking hook (e.g., libraries to specify before the final link)
# we don't implement this currently
sub link_after_cil {
    my ($self, $psrcs, $dest, $ppargs, $ccargs, $ldargs) = @_;
    my @srcs = @{$psrcs};
    my @libs = @{$ldargs};
    my @cargs = @{$ccargs};

    return $self->SUPER::link_after_cil(\@srcs, $dest, $ppargs,
                                            \@cargs, \@libs);
}


sub printHelp {
    my ($self) = @_;
    my @cmd = ($self->{COMPILER});
    print <<EOF;

Usage: xmhfcil [options] <source-files>...

Front end:

--save-temps[=<dir>]  Save intermediate files (target directory optional).
--merge               Operate in cil merge mode.


EOF
    $self->runShell(@cmd); 
}
