#!/bin/sh
if ! type "agda" > /dev/null || [ ! `agda -V | sed "s/[^2]*//"` = "2.5.1" ]; then
  cabal update
  cabal install alex happy cpphs
  git clone https://github.com/agda/agda --depth=1
  cd agda
  cabal install
  cd ..
  mkdir -p $HOME/.agda
  cp libraries-2.6.0 $HOME/.agda/
  cd $HOME/.agda/
  git clone -b experimental https://github.com/agda/agda-stdlib --depth=1
  cd -
fi
