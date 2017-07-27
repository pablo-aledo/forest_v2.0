#!/bin/bash 

cp forest.tar.gz forest_$1.tar.gz
cat install_template.sh | sed "s/%version%/$1/g" > install_$1.sh
cat Makefile_template | sed "s/%version%/$1/g" > Makefile


