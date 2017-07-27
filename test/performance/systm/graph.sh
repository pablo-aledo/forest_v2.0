#!/bin/bash 


rm graph.csv

(
for a in `seq 2 10 2500`
do 
	echo "a = $a" >/dev/stderr

	cat systm_template.cpp | sed "s/%n%/$a/g" > systm.cpp

	g++ systm.cpp -lrt

	line=`./a.out`
	time_real=`echo $line | cut -d" " -f1`
	rank=`echo $line | cut -d" " -f2`

	echo $rank "," $time_real >> graph.csv
	echo $rank "," $time_real

done
) | feedgnuplot --stream --line
