( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( Concat( Concat( Concat( Concat( Concat x1  "abec"  )  x2  )  t1  ) ( Concat "ab"  z1  )  ) ( Concat( Concat "cd"  z2  )  t3  )  ) ( Concat( Concat( Concat( Concat( Concat x2  "dcba"  )  x1  )  t2  ) ( Concat z1  "ba"  )  ) ( Concat z2  "dc"  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 