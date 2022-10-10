( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t () String )
 ( assert ( =( Concat( Concat "bacd"  z  ) ( Concat( Concat x1  "abc"  )  x2  )  ) ( Concat( Concat z  "cdba"  ) ( Concat( Concat( Concat x2  "bba"  )  x1  )  t  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( >( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 