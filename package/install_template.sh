#!/bin/bash

[ "`uname -m | grep 64`" ] || ( echo "This version is meant to be run in a x86_64 machine." ); [ "`uname -m | grep 64`" ] || exit;
[ "`which g++`" ] || ( echo "This program needs g++ installed (tested with Ubuntu 4.8.2-19ubuntu1)." ); [ "`which g++`" ] ||  exit;

rm -rf forest*
wget teisa.unican.es/forest/images/forest_%version%.tar.gz -O - | tar -xz
cd forest

export PATH=`pwd`/bin:$PATH
export LD_LIBRARY_PATH=`pwd`/lib:$LD_LIBRARY_PATH
export FOREST_HOME=`pwd`
export LLVM_HOME=`pwd`/tools/llvm-2.9
export CPACHECKER_HOME=`pwd`/tools/CPAchecker-1.3.4-unix

reset
make 
