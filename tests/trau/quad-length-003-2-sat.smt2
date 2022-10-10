( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( assert ( =( Concat( Concat x1  "ab"  )  x2  ) ( Concat( Concat x2  "ba"  )  x1  )  ) )
 ( assert ( >( Length x1  )  32000  ) )
 ( check-sat )
 