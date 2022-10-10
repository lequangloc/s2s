( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( assert ( =( Concat( Concat( Concat( Concat t1 ( Concat "ab"  z1  )  ) ( Concat "cd"  z2  )  ) ( Concat x1  "abdc"  )  )  x2  ) ( Concat( Concat( Concat t1 ( Concat z1  "ba"  )  ) ( Concat z2  "dc"  )  ) ( Concat( Concat x2  "dcbb"  )  x1  )  )  ) )
 ( check-sat )
 