( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( Concat( Concat( Concat( Concat( Concat( Concat "ab"  z1  )  t2  ) ( Concat "cd"  z2  )  ) ( Concat x1  "abdc"  )  )  x2  )  t3  ) ( Concat( Concat( Concat( Concat( Concat z1  "ba"  )  t2  ) ( Concat z2  "dc"  )  ) ( Concat( Concat x2  "dcba"  )  x1  )  )  t1  )  ) )
 ( assert ( >( Length x1  )  32000  ) )
 ( check-sat )
 