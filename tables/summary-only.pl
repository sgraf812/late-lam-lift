#!/usr/bin/perl

use strict;
use warnings;

my $cols = scalar(@ARGV)-1;

my $skipped = 0;
while (<STDIN>) {
	last if /\\hline/;
}
while (<STDIN>) {
	s/^(.*?) &/\\totalname{$1} &/;
	print;
}
