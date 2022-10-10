( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( Concat( Concat "bacd"  z  ) ( Concat( Concat x1  "ab"  )  x2  )  ) ( Concat( Concat z  "cdba"  ) ( Concat( Concat( Concat x2  "ba"  )  x1  )  t  )  )  ) )
 ( check-sat )
 