( declare-fun  x1 () String )
 ( declare-fun  x2 () String )
 ( declare-fun  z1 () String )
 ( declare-fun  z2 () String )
 ( declare-fun  t1 () String )
 ( declare-fun  t2 () String )
 ( assert ( =( Concat( Concat( Concat( Concat( Concat "abb"  z1  )  t2  ) ( Concat "cd"  z2  )  ) ( Concat x1  "abdc"  )  )  x2  ) ( Concat( Concat( Concat( Concat z1  "baa"  )  t1  ) ( Concat z2  "dc"  )  ) ( Concat( Concat x2  "dcba"  )  x1  )  )  ) )
 ( check-sat )
 