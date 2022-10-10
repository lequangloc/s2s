( declare-fun  x31 () String )
 ( declare-fun  x42 () String )
 ( declare-fun  z () String )
 ( assert ( =( Concat( Concat( Concat x31  "abbc"  )  x42  )  z  ) ( Concat( Concat( Concat x42  "ccba"  )  x31  )  "ab"  )  ) )
 ( check-sat )
 