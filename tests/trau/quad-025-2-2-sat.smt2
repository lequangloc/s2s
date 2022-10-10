( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( Concat( Concat x1  z  )  x2  ) ( Concat( Concat x2  t  )  x1  )  ) )
 ( check-sat )
 