( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( Concat( Concat( Concat "abc"  z  ) ( Concat( Concat x1  "abvv"  )  x2  )  )  t2  ) ( Concat( Concat z  "vba"  ) ( Concat( Concat( Concat x2  "dcba"  )  x1  )  t1  )  )  ) )
 ( check-sat )
 