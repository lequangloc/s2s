( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( Concat( Concat( Concat "ab"  z1  ) ( Concat( Concat x1  "abdc"  )  x2  )  ) ( Concat( Concat "cd"  z2  )  t2  )  ) ( Concat( Concat( Concat z1  "ba"  ) ( Concat( Concat x2  "dcca"  )  x1  )  ) ( Concat( Concat z2  "dc"  )  t1  )  )  ) )
 ( check-sat )
 