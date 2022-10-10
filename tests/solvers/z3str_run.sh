
C_INCLUDE_PATH=. timeout 180 ./Z3-str.py -f $1
if [ $? -eq 124 ]; then
    printf "Result: (UNKNOWN, 180(seconds))\n"
else
    printf ""
  fi
