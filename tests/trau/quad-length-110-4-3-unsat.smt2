( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( Concat( Concat( Concat( Concat "ab"  z1  )  "a"  ) ( Concat( Concat x1  "abdc"  )  x2  )  ) ( Concat( Concat "cd"  z2  )  t3  )  ) ( Concat( Concat( Concat( Concat z1  "bv"  )  t2  ) ( Concat( Concat x2  "dcba"  )  x1  )  ) ( Concat( Concat z2  "dc"  ) ( Concat t1  "gh"  )  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 