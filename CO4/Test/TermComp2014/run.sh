#!/bin/bash

if [ $# -lt 3 ]
then
  echo "Syntax: $0 CMD TIMEOUT UPPER_BITWIDTH [OPTIONS] -- [FILES]"
  exit 1
fi
  
CMD=$1
TIMEOUT=$2
UPPER_BITWIDTH=$3
OPTIONS=""

shift 3

while [ $# -gt 0 ]
do
  if [ $1 == "--" ]
  then
    shift 1
    break
  fi

  OPTIONS="${OPTIONS} $1"

  shift 1
done

if [ $# -eq 0 ]
then
  echo "$0: no input files found (did you forget \"--\")"
  exit 1
fi

NUM_TERMINATES=0
DONT_KNOW=""

while [ $# -gt 0 ]
do
  FILE=$1
  LOG_FILE=$(basename ${FILE}).log

  for BITWIDTH in $(seq 0 ${UPPER_BITWIDTH})
  do
    CALL="${CMD} --model ${BITWIDTH} ${OPTIONS} ${FILE}"
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
