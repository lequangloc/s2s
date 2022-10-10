( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( assert ( =( Concat( Concat( Concat( Concat "ab"  z1  ) ( Concat t1 ( Concat "cd"  z2  )  )  ) ( Concat x1  "abdc"  )  )  x2  ) ( Concat( Concat( Concat z1  "bc"  ) ( Concat t1 ( Concat z2  "dc"  )  )  ) ( Concat( Concat x2  "dcba"  )  x1  )  )  ) )
 ( check-sat )
 