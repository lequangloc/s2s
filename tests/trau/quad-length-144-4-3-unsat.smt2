( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( assert ( =( Concat( Concat( Concat( Concat x1  "abdc"  )  x2  ) ( Concat( Concat "cb"  z1  )  t3  )  ) ( Concat( Concat "cd"  z2  )  t2  )  ) ( Concat( Concat( Concat( Concat x2  "dcba"  )  x1  ) ( Concat( Concat z1  "ba"  )  "c"  )  ) ( Concat( Concat z2  "dc"  )  t1  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 