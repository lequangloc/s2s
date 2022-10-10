
C_INCLUDE_PATH=. timeout 45 ./s2str -to-smt2 -to-smt2-trau $1
if [ $? -eq 124 ]; then
    printf "Result: (UNKNOWN, 45(seconds))\n"
else
    printf ""
  fi
