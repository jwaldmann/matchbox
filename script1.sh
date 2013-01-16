#!/bin/bash

pathMB="/home/eric/NewRepair/trunk/TRS/code/dist/build/mb/mb"

#pathFiles="/home/eric/NewRepair/trunk/TRS/files/TRS_Standard/ -name '*.xml'"

pathFiles="/home/eric/NewRepair/trunk/TRS/files/TRS_Standard/"

logfile=all.log

touch $logfile

find $pathFiles -name '*.xml' | while read file;
do
	echo $file >> $logfile
	timeout 180 $pathMB $file  >> $logfile 2>&1
	echo " "
done


