( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( Concat( Concat( Concat x1  "abc"  )  x2  )  z  ) ( Concat( Concat( Concat x2  "bab"  )  x1  )  t  )  ) )
 ( check-sat )
 