#!/bin/bash

# get prerequisites (not from hackage, but current versions from github):

box=$(pwd)/sand

cabal sandbox init --sandbox $box

rm -rf build ; mkdir build ; pushd build

for arch in minisat-haskell-bindings satchmo haskell-obdd smt-lib satchmo-smt haskell-tpdb transformer-combinators
do
    git clone  https://github.com/jwaldmann/$arch.git
    pushd $arch
    cabal sandbox init --sandbox $box
    cabal install
    popd
done

for arch in satchmo-core co4
do
    git clone https://github.com/apunktbau/$arch.git
    pushd $arch
    cabal sandbox init --sandbox $box
    cabal install 
    popd
done
    

popd

# this uses mb.cabal and builds into sandbox

cabal configure && cabal build
