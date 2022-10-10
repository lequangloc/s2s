( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( Concat( Concat x1 ( Concat "ab"  z  )  )  x2  ) ( Concat( Concat x2 ( Concat "ba"  t  )  )  x1  )  ) )
 ( check-sat )
 