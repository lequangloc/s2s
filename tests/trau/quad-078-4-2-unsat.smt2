( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( Concat( Concat( Concat( Concat( Concat "bb"  z1  ) ( Concat "cd"  z2  )  )  t2  ) ( Concat x1  "abdc"  )  )  x2  ) ( Concat( Concat( Concat( Concat z1  "ba"  ) ( Concat z2  "dc"  )  )  t1  ) ( Concat( Concat x2  "dcba"  )  x1  )  )  ) )
 ( check-sat )
 