#!/bin/bash

pathMB="dist/build/mb/mb"
pathFiles="data/filesPaper"

options="--bits=5 --parallel --dp-fromtop "

logfile_compress=all_dp.log
our_log=small_dp.log

touch $logfile_compress
touch $our_log


find $pathFiles -name '*.xml' | while read file;
do
	echo $file
	echo $file >> $logfile_compress
	echo -n $file >> $our_log

	START=$(date +%s)
	timeout 60 $pathMB $file $options >> $logfile_compress 
	if [ $? -ne 0 ]; then
		echo -n "    TIMEOUT    " >> $our_log
	else
		echo -n "    SUCCESS    " >> $our_log
	fi
	END=$(date +%s)
	DIFF=$(( $END - $START )) 
	echo $DIFF >> $our_log
done


