( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( declare-fun  t4 () String )
 ( declare-fun  t5 () String )
 ( declare-fun  t6 () String )
 ( declare-fun  t7 () String )
 ( assert ( =( Concat( Concat( Concat( Concat "ab"  z  ) ( Concat x1  "abdc"  )  )  x2  )  t3  ) ( Concat( Concat z  "ba"  ) ( Concat( Concat( Concat x2  "dcba"  )  x1  ) ( Concat( Concat t6  t1  ) ( Concat( Concat t7  t5  ) ( Concat t2  t4  )  )  )  )  )  ) )
 ( assert ( >( Length x1  )  32000  ) )
 ( assert ( >( Length z  )  16000  ) )
 ( check-sat )
 