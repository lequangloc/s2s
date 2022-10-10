( declare-fun  x7 () String )
 ( declare-fun  x8 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( declare-fun  x () String )
 ( assert ( =( Concat( Concat( Concat( Concat x7  "abbc"  )  x8  )  z  )  x  ) ( Concat( Concat( Concat( Concat x8  "cdba"  )  x7  )  "abc"  )  t  )  ) )
 ( check-sat )
 