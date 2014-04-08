#!/bin/bash

if [ $# -lt 5 ]
then
  echo "Syntax: $0 CMD TIMEOUT UPPER_BITWIDTH NUM_PRECEDENCES NUM_PATTERNS [FILES] ..."
  exit 1
fi
  
CMD=$1
TIMEOUT=$2
UPPER_BITWIDTH=$3
NUM_PRECEDENCES=$4
NUM_PATTERNS=$5

NUM_TERMINATES=0
DONT_KNOW=""

shift 5

while [ $# -gt 0 ]
do
  FILE=$1
  LOG_FILE=$(basename ${FILE}).log

  for BITWIDTH in $(seq 0 ${UPPER_BITWIDTH})
  do
    CALL="${CMD} --model ${BITWIDTH} --precedences ${NUM_PRECEDENCES} --patterns ${NUM_PATTERNS} ${FILE}"
    echo Calling ${CALL}

    /usr/bin/timeout --signal=SIGKILL ${TIMEOUT} ${CALL} &> ${LOG_FILE}
    if [ $? -eq 0 ]
    then
      echo Terminates
      NUM_TERMINATES=`expr 1 + ${NUM_TERMINATES}`
      break
    fi

    if [ ${BITWIDTH} -eq ${UPPER_BITWIDTH} ]
    then
      DONT_KNOW="${DONT_KNOW}\n${FILE}"
    fi
  done
  shift 1
done

echo ${NUM_TERMINATES} terminations
if [ ! -z ${DONT_KNOW} ]
then
  echo -e "\nUnknown ${DONT_KNOW}"
fi
