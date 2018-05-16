#!/bin/sh

for arg in $*
do
    ~/SizeChangeTool/sizechange.native $arg
    size=$((`expr length $arg`-4))
    fil=`expr substr $arg 1 $size`
    dkcheck -nc -sz -nl -q $fil.dk 2>&1 | xargs ~/SizeChangeTool/analyse.sh
done
