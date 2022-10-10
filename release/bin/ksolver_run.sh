timeout 600 ./ksolver $1
if [ $? -eq 124 ]; then
    printf "Result: (UNKNOWN, 600(seconds))\n"
else
    printf ""
  fi
