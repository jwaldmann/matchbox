#!/bin/bash

pathMB="/home/eric/NewRepair/trunk/TRS/code/dist/build/mb/mb"
pathFiles="/home/eric/NewRepair/trunk/TRS/files/SRS_Relative/ICFP_2010_relative"

#pathFiles="data/TRS_Standard/Transformed_CSR_04"

logfile_nocompress=testing_no.log
logfile_simplecompress=all_ICFP_2010_relative.log
logfile_compress=testing_compress.log
logfile_done=log

options_for_all="--bits=4 -s"

touch $logfile_nocompress
touch $logfile_simplecompress
touch $logfile_compress

find $pathFiles -name '*.xml' | while read file;
do
	echo $file 
	echo $file  >> $logfile_nocompress
	timeout 60 $pathMB $file $options_for_all >> $logfile_nocompress #2>&1
	if [ $? -eq 124 ]; then
		echo "TIMEOUT" >> $logfile_nocompress
	else
		echo "SUCCESS" >> $logfile_nocompress
	fi
	echo $file >> $logfile_compress
	timeout 60 $pathMB $file $options_for_all -c >> $logfile_compress #2>&1
	if [ $? -eq 124 ]; then
		echo "TIMEOUT" >> $logfile_compress
	else
		echo "SUCCESS" >> $logfile_compress
	fi
	echo "done: " $file >>$logfile_done
done


