#!/bin/bash

# https://stackoverflow.com/a/246128/388010
dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

set -e

diffs="base ll ll-c2 ll-c4 ll-c3-4-4 ll-c3-5-6 ll-c3-6-5 ll-c3-8-8"

# Finds the log for the argument
l() {
  ls $dir/logs/$1-20[0-9][0-9]-*.log|tail -n1
}

# Finds the build log for the argument
bl() {
  ls $dir/logs/buildlog-$1-20[0-9][0-9]-*.log|tail -n1
}

# There's no way I know of to just map a function over each element
# of a space-separated list inside in a variable. Hooray for sh!
logs=""
buildlogs=""
for diff in $diffs
do
  logs="$logs $(l $diff)"
  buildlogs="$buildlogs $(bl $diff)"
done

# prunes the given file and puts the result in $1-pruned
# Note that all pruned benchmarks are sensitive to non-deterministic code
# layout changes.
p() {
  prune="(fft2|CS|CSD|FS|S|VS|VSD|VSM)"
  sed -E "/==nofib== $prune/,/Finished making all in $prune/d" $1 > $1-pruned
}

pruned=""
for log in $logs;
do
  p $log
  pruned="$pruned $log-pruned"
done

nofib-analyse --columns=Allocs,Runtime -i 0.1  $pruned > nofib-table-all.txt
nofib-analyse --columns=Allocs,Runtime -l $(l base)-pruned $(l ll)-pruned | ./fixup.pl -4.0 2.0 > $dir/base.tex
nofib-analyse --columns=Allocs,Runtime -l $(l ll)-pruned $(l ll-c2)-pruned | ./fixup.pl -4.0 2.0 > $dir/c2.tex
nofib-analyse --columns=Runtime -l $(l ll)-pruned $(l ll-c3-4-4)-pruned $(l ll-c3-5-6)-pruned $(l ll-c3-6-5)-pruned $(l ll-c3-8-8)-pruned | ./fixup.pl -3.0 3.0 > $dir/c3.tex
nofib-analyse --columns=Runtime -l $(l ll)-pruned $(l ll-c4)-pruned | ./fixup.pl -1.0 1.0 > $dir/c4.tex
nofib-analyse --columns="Comp. Alloc,Comp. Time" -l -i 0.1 $(l base)-pruned $(l ll)-pruned | ./summary-only.pl $logs | grep 'Geometric' | sed -e 's/Geometric Mean/nofib/'> $dir/nofib.tex

for log in $logs;
do
  rm -f $log-pruned
done

./buildlog.pl $(bl base) $(bl ll) > $dir/ghc.tex
