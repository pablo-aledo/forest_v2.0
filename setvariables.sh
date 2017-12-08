#! /bin/bash

# add bin to path
export PATH=$(pwd)/bin/:$PATH
export PATH=/usr/src/llvm-3.7/Debug+Asserts/bin:$PATH

# set environment variables
export LLVM_HOME=/usr/src/llvm-3.7
export FOREST_HOME=$(pwd)
