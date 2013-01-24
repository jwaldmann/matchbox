#!/bin/bash

pathMB="/home/eric/NewRepair/trunk/TRS/code/dist/build/mb/mb"
pathFiles="/home/eric/NewRepair/trunk/TRS/files/SRS_Relative/ICFP_2010_relative"

logfile_nocompress=all_no_ICFP_2010_relative.log
logfile_simplecompress=all_ICFP_2010_relative.log
logfile_compress=all_compress_ICFP_2010_relative.log
logfile_done=all_done.log

touch $logfile_nocompress
touch $logfile_simplecompress
touch $logfile_compress

find $pathFiles -name '*.xml' | while read file;
do
	echo $file 
	echo $file  >> $logfile_nocompress
	timeout 180 $pathMB $file --bits=4 >> $logfile_nocompress 2>&1
	echo $file >> $logfile_simplecompress
	timeout 180 $pathMB $file -k --bits=4 >> $logfile_simplecompress 2>&1
	echo $file >> $logfile_compress
	timeout 180 $pathMB $file -c --bits=4 >> $logfile_compress 2>&1
	echo "done: " $file >>$logfile_done
done


