( declare-fun  x7 () String )
 ( declare-fun  x8 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( assert ( =( Concat( Concat( Concat( Concat x7  "abbc"  )  x8  )  z  )  x2  ) ( Concat( Concat( Concat( Concat x8  "cbba"  )  x7  )  "ab"  ) ( Concat x1  t  )  )  ) )
 ( check-sat )
 