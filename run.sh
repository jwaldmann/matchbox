#!/bin/bash

TPDB=$HOME/tpdb/tpdb-4.0/SRS/Zantema

for sys in $(cd $TPDB ; find . -name "*.srs")
do
    for solver in boolector satchmo guarded-satchmo
    do
	out=run/$sys
	mkdir -p $(dirname $out)
	echo -n $sys $solver :
	timeout 60 matchbox2015 -b4 --$solver $sys 2>$out.err 1>$out.out
	head -1 $out.out
    done
done
