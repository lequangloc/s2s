( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( Concat( Concat( Concat( Concat "ab"  z  ) ( Concat x1  "addc"  )  )  x2  ) ( Concat t2  t3  )  ) ( Concat( Concat z  "ba"  ) ( Concat( Concat( Concat x2  "dcba"  )  x1  )  t1  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( >( Length z  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 