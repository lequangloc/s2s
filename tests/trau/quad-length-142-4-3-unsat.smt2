( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( Concat( Concat( Concat( Concat x1  "abdc"  )  x2  ) ( Concat "ac"  z1  )  ) ( Concat( Concat "rd"  z2  ) ( Concat t3  t2  )  )  ) ( Concat( Concat( Concat( Concat x2  "dcba"  )  x1  ) ( Concat z1  "ba"  )  ) ( Concat( Concat z2  "dc"  )  t1  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 