( declare-fun  x7 () String )
 ( declare-fun  x8 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( assert ( =( Concat( Concat( Concat( Concat x7  "abdbc"  )  x8  )  z  ) ( Concat x1  x2  )  ) ( Concat( Concat( Concat( Concat x8  "cbbad"  )  x7  )  "ab"  )  t  )  ) )
 ( check-sat )
 