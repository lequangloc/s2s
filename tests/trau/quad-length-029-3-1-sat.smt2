( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( Concat( Concat x1 ( Concat z  z  )  )  x2  ) ( Concat( Concat( Concat x2  "ba"  )  x1  )  t  )  ) )
 ( assert ( >( Length x1  )  32000  ) )
 ( check-sat )
 