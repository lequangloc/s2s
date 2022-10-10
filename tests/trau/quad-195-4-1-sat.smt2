( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( assert ( =( Concat( Concat( Concat "ab"  z1  ) ( Concat( Concat x1  "abdc"  )  x2  )  ) ( Concat t1  z2  )  ) ( Concat( Concat( Concat z1  "ba"  ) ( Concat( Concat x2  "dcba"  )  x1  )  ) ( Concat z2  "dc"  )  )  ) )
 ( check-sat )
 