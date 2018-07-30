#!/bin/sh

d="${0%/*}"
for arg in $*
do
    $d/bin/tpdb_to_dk.native $arg
    size=$((`expr length $arg`-4))
    fil=`expr substr $arg 1 $size`
    $d/bin/Dedukti/dkcheck.native -nc -sz -nl -q $fil.dk 2>&1 \
    | xargs $d/bin/analyse.sh
done
