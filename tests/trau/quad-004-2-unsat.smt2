( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( assert ( =( Concat( Concat x1  "aa"  )  x2  ) ( Concat( Concat x2  "ba"  )  x1  )  ) )
 ( check-sat )
 