#!/bin/bash -v

# this script puts the matchbox executable
# in a zip file that can be submitted
# to the starexec execution platform

source=MB.hs
exe=MB.exe

target=matchbox2015
# target=matchbox-compress

# name of the binary in the release package 
# will be $target.bin
# note that source release/$target.sh must exist

# -fllvm -fforce-recomp 

ghc --make \
    -O2 -funbox-strict-fields -rtsopts -threaded \
    $source -o $exe

dir=$target-$(date -I)

rm -rf $dir
mkdir -p $dir
mkdir -p $dir/bin

cp -v $exe $dir/bin/$exe
strip $dir/bin/$exe

cp -v release/README $dir
cp -v -P /usr/local/lib64/{libboolector.so,libgcc_s.so.1,libstdc++.so.6,libstdc++.so.6.0.21} $dir/bin/
cp -v release/starexec_run_*.sh $dir/bin/

rm -f $dir.zip

(cd $dir ; zip -r - .) > $dir.zip

# (mkdir $dir ; cd $dir ; unzip  ../$dir.zip)
# unzip $dir.zip

ls -l $dir
ls -l $dir.zip
unzip -l $dir.zip
