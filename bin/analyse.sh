#!/bin/sh

if [ $1 = "SUCCESS" ]
then 
    if [ $7 = "TERMINATING" ]
    then
        echo "YES"
    else
        echo "MAYBE"
    fi
else
    echo "MAYBE"
fi
