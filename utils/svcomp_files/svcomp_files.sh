#!/bin/bash 

SRC_DIR=/media/DATA/Work/forest/svcomp/c
DST_DIR=/media/DATA/Work/forest/disk/release/test/svcomp_16_2
BAS_DIR=/media/DATA/Work/forest/disk/release

find $DST_DIR -type f -not -name list -delete
find $DST_DIR -type d -empty -delete

escape(){
	echo $1 | sed 's/\//\\\//g'
}

for listname in `cd $DST_DIR; find -name list`
do 
	category=`echo $listname | sed 's/^..\([^\/]*\)\/list/\1/g'`
	cat $DST_DIR/$listname | sed "s/^\(.*\)/cp $(escape $SRC_DIR)\/\1 $(escape $DST_DIR)\/$category\//g" 
done | bash




for listname in `cd $DST_DIR; find -name list`
do 
	category=`echo $listname | sed 's/^..\([^\/]*\)\/list/\1/g'`
	cd $DST_DIR/$category

	ls *.c && for a in *.c; do mkdir `basename $a .c`; mv $a `basename $a .c`; done
	ls *.i && for a in *.i; do mkdir `basename $a .i`; mv $a `basename $a .i`; done

	first=`ls | grep -v list | head -n1`

	cd $first
	echo '<?xml version="1.0"?>' > config.xml
	echo '<options>' >> config.xml
	echo '<option key="svcomp" value="true"/>'  >> config.xml
	echo '<option key="file" value="%name%"/>'  >> config.xml
	echo '</options>'  >> config.xml
	cd ..

	for a in `ls | grep -v list`; do \cp $first/config.xml $a; done
	for a in `ls | grep -v list`; do cd $a; name=`ls | grep -v config | head -n1`; sed -i s/%name%/$name/g config.xml; cd ..; done

	cd ..
done

cd $BAS_DIR

for category in `cd $DST_DIR; find -name list | sed 's/^..\([^\/]*\)\/list/\1/g'`
do 
	echo "$category:" >> $BAS_DIR/Makefile
	cd $BAS_DIR
	find -name config.xml | grep svcomp_16_2 | grep $category | sed 's/^/\t@forest /g' >> $BAS_DIR/Makefile
done


