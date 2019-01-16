#!/usr/bin/perl

use strict;
use warnings;

my $min = $ARGV[0];
my $max = $ARGV[1];

my $skipped = 0;
my $amps = 0;
while (<STDIN>) {
	last if /\\hline/;

	# remove absolute values
	s/\d+\.\d+( \&|\\\\)/$1/g;

	# any interesting ratio? e.g. not in [$min,$max]
	# also we include all regressions (they have a plus) if that's what is wanted
	my @ratios = /(-?\d{1,2}.\d)\\%/g;
	if ((grep { $_ < $min || $max < $_ } @ratios)) {
		$amps = () = /&/g;
		s/^([^ ]*?) /\\progname{$1} /;
		print;
	} else {
		$skipped++;
	}
}
print "\\andmore{$skipped}" . (" &" x $amps) . " \\\\\n";
print "\\midrule\n";
while (<STDIN>) {
	s/^(.*?) &/\\totalname{$1} &/;
	print;
}
