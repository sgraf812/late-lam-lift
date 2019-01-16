#!/usr/bin/perl

sub sum_stats {
	open(FILE, '<', $_) or die @!;
	# zoom ahead until stage1 has been built
	while (<FILE>) {
		last if m,inplace/bin/ghc-stage1,;
	}
	my $allocs = 0;
	my $time = 0.0;
	while (<FILE>) {
		next unless m!<<ghc: (\d+) bytes, \d+ GCs, \d+/\d+ avg/max bytes residency \(\d+ samples\), \d+M in use, \d+\.\d+ INIT \((\d+\.\d+) elapsed\), \d+\.\d+ MUT \((\d+\.\d+) elapsed\), \d+\.\d+ GC \((\d+\.\d+) elapsed\) :ghc>>!;
		$allocs += $1;
		$time += $2 + $3 + $4;
	}
	close FILE;
	return [$allocs, $time];
}


my @res;
push @res, sum_stats($_) for @ARGV;

my $base = shift @res;

printf '\\totalname{ghc} ';
for my $res (@res) {
	if ($base->[0]) {
		printf '& %+.1f\%% ', ($res->[0]/$base->[0])*100.0-100.0;
	} else {
		printf "& NaN ";
	}
}
for my $res (@res) {
	if ($base->[0]) {
		printf '& %+.1f\%% ', ($res->[1]/$base->[1])*100.0-100.0;
	} else {
		printf "& NaN ";
	}
}
print "\\\\\n";

