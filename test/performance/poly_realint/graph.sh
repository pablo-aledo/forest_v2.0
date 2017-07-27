#!/bin/bash 


rm graph.csv

g++ -DN=2 systm.cpp -lrt
./a.out 
cat /tmp/problem_0.smt2

(
for a in `seq 2 1 100`
do 
	echo "a = $a" >/dev/stderr

	g++ -DN=$a systm.cpp -lrt

	line=`./a.out`
	time=`echo $line | cut -d" " -f1`
	sat=`echo $line | cut -d" " -f2`
	unsat=`echo $line | cut -d" " -f3`

	echo $time,$sat,$unsat >> graph.csv
	echo $time $sat $unsat

done
) | feedgnuplot --stream --line
