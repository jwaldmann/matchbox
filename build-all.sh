#!/bin/bash

# get prerequisites (not from hackage, but current versions from github):

sudo rm -rf build ; mkdir build

pushd build

for arch in minisat minisat-c-bindings
do
    git clone  https://github.com/niklasso/$arch.git
    pushd $arch
    make config
    make
    sudo make install
    popd
done

git clone  https://github.com/niklasso/minisat-haskell-bindings.git
pushd minisat-haskell-bindings
cabal install --extra-lib-dirs=/usr/local/lib --extra-include-dirs=/usr/local/include

popd

cabal install hmatrix-glpk --extra-lib-dirs=/usr/local/lib --extra-include-dirs=/usr/local/include

for arch in satchmo haskell-obdd smt-lib satchmo-smt haskell-tpdb transformer-combinators
do
    git clone  https://github.com/jwaldmann/$arch.git
    pushd $arch
    cabal install --force-reinstalls
    popd
done

for arch in satchmo-core co4
do
    git clone https://github.com/apunktbau/$arch.git
    pushd $arch
    cabal install --force-reinstalls
    popd
done
    

popd

# this uses mb.cabal:

cabal clean && cabal configure && cabal build
