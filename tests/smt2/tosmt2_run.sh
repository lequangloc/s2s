
C_INCLUDE_PATH=. timeout 45 ./s2str -to-smt2 $1
if [ $? -eq 124 ]; then
    printf "Result: (UNKNOWN, 45(seconds))\n"
else
    printf ""
  fi
