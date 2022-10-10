
C_INCLUDE_PATH=. ./norn -timeout=45 $1
if [ $? -eq 124 ]; then
    printf "Result: (UNKNOWN, 45(seconds))\n"
else
    printf ""
  fi
