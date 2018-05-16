#!/bin/sh

if [ $1 = "SUCCESS" -a $7 = "TERMINATING" ]
then
    echo "YES"
else
    echo "MAYBE"
fi
