#!/bin/sh
if ! type "agda" > /dev/null || [ ! `agda -V | sed "s/[^2]*//"` = "2.6.0.1" ]; then
  cabal update
  cabal install alex happy cpphs
  git clone -b v2.6.0.1 https://github.com/agda/agda --depth=1
  cd agda
  cabal install
  cd ..
  mkdir -p $HOME/.agda
  cp libraries-2.6.0.1 $HOME/.agda/
  cd $HOME/.agda/
  git clone -b v1.2 https://github.com/agda/agda-stdlib --depth=1
fi
