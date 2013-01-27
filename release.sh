#!/bin/bash -v

# this script puts the matchbox executable
# in a zip file that can be submitted
# to the termcomp execution platform

source=MB.hs
target=matchbox-compress

# name of the binary in the release package 
# will be $target.bin
# note that source release/$target.sh must exist

ghc --make  \
    -O2 -funbox-strict-fields -rtsopts -threaded \
    $source -o $source.bin

# the release will be place in this directory
dir=$target-$(date -I)
echo $dir

rm -rf $dir 
mkdir -p $dir

cp -v $source.bin $dir/$target.bin
strip $dir/$target.bin

cp -v release/README $dir
cp -v -P release/lib*.so.* $dir
cp -v release/$target.sh $dir/runme

chmod -v +x $dir/runme

rm -f $dir.zip

# (cd $dir ; zip -r - .) > $dir.zip
zip -r - $dir > $dir.zip

rm -rf $dir

# (mkdir $dir ; cd $dir ; unzip  ../$dir.zip)
unzip $dir.zip

ls -l $dir
ls -l $dir.zip
