#! /bin/bash

rm *.ll
rm *.bc

source ../../../setvariables.sh

clang -c -emit-llvm main.c
opt -load /usr/src/llvm-3.7/Debug+Asserts/lib/ForestInstr.so -insert_select_variables < main.bc > with_select_variables.bc

llvm-dis main.bc
llvm-dis with_select_variables.bc

meld main.ll with_select_variables.ll
