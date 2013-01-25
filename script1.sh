#!/bin/bash

pathMB="dist/build/mb/mb"
#pathMB="/home/eric/NewRepair/trunk/TRS/code/dist/build/mb/mb"
pathFiles="/home/eric/NewRepair/trunk/TRS/files/SRS_Relative/ICFP_2010_relative"

#pathFiles="data/TRS_Standard/"

logfile_nocompress=all_no.log
logfile_dp=all_dp.log
logfile_compress=all_compress.log
logfile_done=done.log

sterr_nocompress=sterr_no.log
sterr_dp=sterr_dp.log
sterr_compress=sterr_compress.log

options_for_all="--bits=5 -s"

touch $logfile_nocompress
touch $logfile_dp
touch $logfile_compress
touch $logfile_done

touch $sterr_nocompress
touch $sterr_dp
touch $sterr_compress

find $pathFiles -name '*.xml' | while read file;
do
	echo $file
	echo $file >> $logfile_nocompress
	echo $file >> $sterr_nocompress
	
	timeout 60 $pathMB $file $options_for_all >> $logfile_nocompress 2>> $sterr_nocompress
	if [ $? -ne 0 ]; then
		echo "TIMEOUT" >> $logfile_nocompress
	else
		echo "SUCCESS" >> $logfile_nocompress
	fi
	echo $file >> $logfile_compress
	echo $file >> $sterr_compress
	timeout 60 $pathMB $file $options_for_all -c >> $logfile_compress 2>> $sterr_compress
	if [ $? -ne 0 ]; then
		echo "TIMEOUT" >> $logfile_compress
	else
		echo "SUCCESS" >> $logfile_compress
	fi
	echo $file >> $logfile_dp
	echo $file >> $sterr_dp
	timeout 60 $pathMB $file $options_for_all -c --dp >> $logfile_dp 2>> $sterr_dp
	if [ $? -ne 0 ]; then
		echo "TIMEOUT" >> $logfile_dp
	else
		echo "SUCCESS" >> $logfile_dp
	fi
	echo "done: " $file >>$logfile_done
done


