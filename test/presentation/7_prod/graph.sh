#!/bin/bash 


rm graph.csv

(
for a in `seq 1 30`
do

	cat prod_template.c | sed "s/%n%/$a/g" > prod.c
	forest -klee 2>&1 >/dev/null
	time_klee=`echo 'select time_ms from klee order by rowid desc limit 1;' | sqlite3 /tmp/forest/database.db `
	forest -test false -run -unconstrained 2>&1 >/dev/null
	time_forest=`echo 'select value from measurements where key="time_ms";' | sqlite3 /tmp/forest/database.db `

	echo $time_klee "," $time_forest >> graph.csv
	echo $time_klee "," $time_forest 


done
) | feedgnuplot --stream --line
