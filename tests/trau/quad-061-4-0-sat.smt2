( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( assert ( =( Concat( Concat( Concat( Concat "ab"  z1  ) ( Concat "cd"  z2  )  ) ( Concat x1  "abdc"  )  )  x2  ) ( Concat( Concat( Concat z1  "ba"  ) ( Concat z2  "dc"  )  ) ( Concat( Concat x2  "dcba"  )  x1  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( assert ( =( Length x1  ) ( Length x2  )  ) )
 ( check-sat )
 