( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( Concat( Concat( Concat "bacd"  z  ) ( Concat( Concat x1  "ab"  )  x2  )  )  t2  ) ( Concat( Concat z  "cdba"  ) ( Concat( Concat( Concat x2  "ba"  )  x1  )  t1  )  )  ) )
 ( check-sat )
 