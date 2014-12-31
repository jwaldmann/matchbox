#!/bin/bash

TPDB=$HOME/tpdb/tpdb-4.0/SRS

bits=4

for sys in $(cd $TPDB ; find . -name "*.srs" | sort -r)
do
    for solver in boolector satchmo guarded-satchmo
    do
	out=run/$solver/$bits/$sys
	mkdir -p $(dirname $out)
	echo -n $sys $solver :
	timeout 60 matchbox2015 --$solver --bits $bits $TPDB/$sys 2>$out.err 1>$out.out
	echo $(head -1 $out.out)
    done
done
