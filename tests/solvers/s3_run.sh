
C_INCLUDE_PATH=. timeout 180 ./run-s3.py -f $1
if [ $? -eq 124 ]; then
    printf "Result: (UNKNOWN, 180(seconds))\n"
else
    printf ""
  fi
