#!/bin/bash

pathMB="/home/eric/NewRepair/trunk/TRS/code/dist/build/mb/mb"

#pathFiles="/home/eric/NewRepair/trunk/TRS/files/TRS_Standard/ -name '*.xml'"

logfile=all.log

rm -f $logfile
touch $logfile

find /home/eric/NewRepair/trunk/TRS/files/TRS_Standard/ -name '*.xml' | while read file;
do
	echo $file >> $logfile
	timeout 180 $pathMB $file  >> $logfile 2>&1
	echo " "
done


