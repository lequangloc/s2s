( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( declare-fun  t3 () String )
 ( declare-fun  t4 () String )
 ( assert ( =( Concat( Concat( Concat( Concat( Concat x1  "ablc"  )  x2  )  t1  ) ( Concat( Concat "ab"  z1  )  t4  )  ) ( Concat "cd"  z2  )  ) ( Concat( Concat( Concat( Concat( Concat x2  "dcba"  )  x1  )  t2  ) ( Concat( Concat z1  "ba"  )  t3  )  ) ( Concat z2  "dc"  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 