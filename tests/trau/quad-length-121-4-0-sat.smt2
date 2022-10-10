( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( assert ( =( Concat( Concat( Concat( Concat x1  "abdc"  )  x2  ) ( Concat "ab"  z1  )  ) ( Concat "cd"  z2  )  ) ( Concat( Concat( Concat( Concat x2  "dcba"  )  x1  ) ( Concat z1  "ba"  )  ) ( Concat z2  "dc"  )  )  ) )
 ( assert ( >( Length x1  )  16000  ) )
 ( check-sat )
 